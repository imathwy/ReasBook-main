import Mathlib
import StacksProject_2024.stacks_project.Chap18.Lemma_18_30_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open CategoryTheory.Limits.CoproductsFromFiniteFiltered
open scoped CategoryTheory.GrothendieckTopology.SheafifiedRepresentable

noncomputable section

universe u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J (Type u)]
variable [HasFiniteCoproducts (Sheaf J (Type u))]
variable (B : Set C)
variable [J.HasQuasiCompactBasisWithQuasiCompactFiberProducts B]

/-- A sheaf of sets has a finite basis coequalizer presentation if it is isomorphic to the
coequalizer of two maps between finite coproducts of sheafified representables `h_U^#` built from
objects of `B`. -/
abbrev HasFiniteBasisSheafifiedRepresentableCoequalizerPresentation
    (ℱ : Sheaf J (Type u)) : Prop :=
  ∃ (n m : ℕ) (U : Fin n → C) (V : Fin m → C),
    let _ : HasColimitsOfShape (Discrete (Fin m)) (Sheaf J (Type u)) :=
      Limits.hasColimitsOfShape_discrete (C := Sheaf J (Type u)) (Fin m)
    let _ : HasColimitsOfShape (Discrete (Fin n)) (Sheaf J (Type u)) :=
      Limits.hasColimitsOfShape_discrete (C := Sheaf J (Type u)) (Fin n)
    let _ : HasColimitsOfShape WalkingParallelPair (Sheaf J (Type u)) :=
      (Sheaf.instHasColimitsOfShape :
        HasColimitsOfShape WalkingParallelPair (Sheaf J (Type u)))
    ∃ (left right :
      (∐ fun j : Fin m ↦ h[V j]^#[J]) ⟶
        (∐ fun i : Fin n ↦ h[U i]^#[J]))
      (_ : ℱ ≅ coequalizer left right),
        (∀ i, U i ∈ B) ∧
          ∀ j, V j ∈ B

/-- Helper for Lemma 18.30.7: every sheaf admits one possibly infinite coequalizer presentation
whose source and target are coproducts of basis sheafified representables. -/
lemma existsBasisSheafifiedRepresentableInfiniteCoequalizerPresentation
    (ℱ : Sheaf J (Type u)) :
    ∃ (A K : Type u) (U : A → C) (V : K → C)
      (left right :
        (∐ fun j : K ↦ h[V j]^#[J]) ⟶
          (∐ fun i : A ↦ h[U i]^#[J]))
      (_ : ℱ ≅ coequalizer left right),
        (∀ i, U i ∈ B) ∧
          ∀ j, V j ∈ B := by
  let _ : HasColimitsOfShape WalkingParallelPair (Sheaf J (Type u)) := Sheaf.instHasColimitsOfShape
  -- Start from the locally surjective basis coproduct map supplied by Lemma `18.30.6 (1)`.
  obtain ⟨A, U, hU, -, φ, hφ⟩ :=
    exists_locallySurjective_from_coproduct_basis_sheafifiedRepresentables (J := J) B ℱ
  -- Apply the same basis coproduct presentation to the pullback of that map with itself.
  obtain ⟨K, V, hV, -, ψ, hψ⟩ :=
    exists_locallySurjective_from_coproduct_basis_sheafifiedRepresentables (J := J) B
      (pullback φ φ)
  let left :
      (∐ fun j : K ↦ h[V j]^#[J]) ⟶
        (∐ fun i : A ↦ h[U i]^#[J]) :=
    ψ ≫ pullback.fst φ φ
  let right :
      (∐ fun j : K ↦ h[V j]^#[J]) ⟶
        (∐ fun i : A ↦ h[U i]^#[J]) :=
    ψ ≫ pullback.snd φ φ
  have hφeq : left ≫ φ = right ≫ φ := by
    -- The pullback projections equalize the locally surjective map `φ`.
    dsimp [left, right]
    simp [Category.assoc, pullback.condition]
  have hcofork₀ : IsColimit (Cofork.ofπ φ pullback.condition) :=
    CategoryTheory.Sheaf.isColimitCoforkOfIsLocallySurjective φ hφ
  have hcofork : IsColimit (Cofork.ofπ φ hφeq) := by
    -- Any cocone over the restricted parallel pair descends uniquely along `φ`.
    refine Cofork.IsColimit.ofExistsUnique ?_
    intro s
    have hsq : left ≫ s.π = right ≫ s.π := s.condition
    letI : Epi ψ := (Sheaf.isLocallySurjective_iff_epi ψ).1 hψ
    have hpb : pullback.fst φ φ ≫ s.π = pullback.snd φ φ ≫ s.π := by
      apply (cancel_epi ψ).1
      simpa [left, right, Category.assoc] using hsq
    exact Cofork.IsColimit.existsUnique hcofork₀ s.π hpb
  let e : ℱ ≅ coequalizer left right :=
    hcofork.coconePointUniqueUpToIso (colimit.isColimit (parallelPair left right))
  exact ⟨A, K, U, V, left, right, e, hU, hV⟩

/-- Helper for Lemma 18.30.7: the sheafified-representable Hom/sections equivalence is natural in
the target sheaf. -/
private theorem uliftSheafifiedRepresentableHomEquiv_naturality_right
    {W : C} {𝒢 ℋ : Sheaf J (Type u)} (β : h[W]^#[J] ⟶ 𝒢) (α : 𝒢 ⟶ ℋ) :
    J.uliftSheafifiedRepresentableHomEquiv ℋ W (β ≫ α) =
      (((sheafSections J (Type u)).obj (op W)).map α)
        (J.uliftSheafifiedRepresentableHomEquiv 𝒢 W β) := by
  -- The owner equivalence is defined by evaluating the morphism on `W`, so target naturality is
  -- definitional.
  rfl

/-- Helper for Lemma 18.30.7: a morphism from one basis sheafified representable into a coproduct
of basis sheafified representables factors through a single summand. -/
lemma basisSheafifiedRepresentableMapFactorsThroughSingleSummand
    {W : C} (hW : W ∈ B) {A : Type u} (U : A → C)
    [HasColimitsOfShape (Discrete A) (Sheaf J (Type u))]
    (g : h[W]^#[J] ⟶ (∐ fun a : A ↦ h[U a]^#[J])) :
    ∃ a : A, ∃ g_a : h[W]^#[J] ⟶ h[U a]^#[J],
      g_a ≫ Limits.Sigma.ι (fun b : A ↦ h[U b]^#[J]) a = g := by
  let G := ((sheafSections J (Type u)).obj (op W))
  have hq : J.QuasiCompactObject W :=
    HasQuasiCompactBasisWithQuasiCompactFiberProducts.quasiCompactObject
      (J := J) (B := B) hW
  have hpres : PreservesColimitsOfShape (Discrete A) G :=
    quasiCompactObject_sheaf_sections_preserves_coproducts (J := J) W hq A
  let F : Discrete A ⥤ Sheaf J (Type u) := Discrete.functor (fun a : A ↦ h[U a]^#[J])
  let x : G.obj (∐ fun a : A ↦ h[U a]^#[J]) :=
    J.uliftSheafifiedRepresentableHomEquiv _ W g
  let t : Cocone (F ⋙ G) := G.mapCocone (colimit.cocone F)
  have ht : IsColimit t := isColimitOfPreserves G (colimit.isColimit F)
  -- The preserved coproduct of sections is still a concrete colimit, so the given section comes
  -- from one tagged summand.
  obtain ⟨a, ya, hya⟩ := CategoryTheory.Types.jointly_surjective_of_isColimit ht x
  let g_a : h[W]^#[J] ⟶ h[U a.as]^#[J] :=
    (J.uliftSheafifiedRepresentableHomEquiv (h[U a.as]^#[J]) W).symm ya
  refine ⟨a.as, g_a, ?_⟩
  apply (J.uliftSheafifiedRepresentableHomEquiv _ W).injective
  -- After applying sections over `W`, the factorization statement is exactly the representative
  -- identity coming from the preserved coproduct colimit.
  rw [uliftSheafifiedRepresentableHomEquiv_naturality_right (J := J) (β := g_a)
    (α := Limits.Sigma.ι (fun b : A ↦ h[U b]^#[J]) a.as)]
  have hsection :
      G.map (Limits.Sigma.ι (fun b : A ↦ h[U b]^#[J]) a.as) ya = x := by
    simpa [t, F] using hya
  simpa [g_a, x] using hsection

/-- Helper for Lemma 18.30.7: a one-stage diagram gives a degenerate filtered colimit
presentation. -/
lemma exists_filteredColimitPresentation_of_hasFiniteBasisSheafifiedRepresentableCoequalizerPresentation
    (ℱ : Sheaf J (Type u))
    (hℱ : HasFiniteBasisSheafifiedRepresentableCoequalizerPresentation J B ℱ) :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I)
      (pres : ColimitPresentation I ℱ),
        ∀ i, HasFiniteBasisSheafifiedRepresentableCoequalizerPresentation J B (pres.diag.obj i) := by
  let I : Type u := Discrete (ULift PUnit)
  let pres : ColimitPresentation I ℱ :=
    { diag := Functor.const I ℱ
      ι :=
        { app := fun _ ↦ 𝟙 ℱ
          naturality := by
            intro X Y f
            simp }
      isColimit := by
        -- The constant one-object diagram has colimit `ℱ` itself.
        refine IsColimit.mk ?_ ?_ ?_
        · intro s
          exact s.ι.app ⟨ULift.up PUnit.unit⟩
        · intro s j
          cases j
          simp
        · intro s m hm
          simpa using hm ⟨ULift.up PUnit.unit⟩ }
  refine ⟨I, inferInstance, inferInstance, pres, ?_⟩
  intro i
  cases i
  simpa [pres]

/-- Helper for Lemma 18.30.7: transport a finite basis sheafified-representable coequalizer
presentation across an isomorphism of sheaves. -/
private theorem hasFiniteBasisSheafifiedRepresentableCoequalizerPresentation_of_iso
    {X Y : Sheaf J (Type u)} (e : X ≅ Y)
    (hX : HasFiniteBasisSheafifiedRepresentableCoequalizerPresentation J B X) :
    HasFiniteBasisSheafifiedRepresentableCoequalizerPresentation J B Y := by
  -- Reuse the same finite coequalizer data and transport only the identifying isomorphism.
  rcases hX with ⟨n, m, U, V, left, right, i, hU, hV⟩
  exact ⟨n, m, U, V, left, right, e.symm ≪≫ i, hU, hV⟩

/-- Helper for Lemma 18.30.7: a finite-index coequalizer presentation over arbitrary finite index
types can be reindexed into the `Fin n` form used by the public predicate. -/
private theorem hasFiniteBasisSheafifiedRepresentableCoequalizerPresentation_of_finiteTypes
    {X : Sheaf J (Type u)}
    {A K : Type u} [Fintype A] [Fintype K]
    (U : A → C) (V : K → C)
    (left right :
      (∐ fun j : K ↦ h[V j]^#[J]) ⟶
        (∐ fun i : A ↦ h[U i]^#[J]))
    (e : X ≅ coequalizer left right)
    (hU : ∀ i, U i ∈ B) (hV : ∀ j, V j ∈ B) :
    HasFiniteBasisSheafifiedRepresentableCoequalizerPresentation J B X := by
  let _ : HasColimitsOfShape (Discrete A) (Sheaf J (Type u)) :=
    Limits.hasColimitsOfShape_discrete (C := Sheaf J (Type u)) A
  let _ : HasColimitsOfShape (Discrete K) (Sheaf J (Type u)) :=
    Limits.hasColimitsOfShape_discrete (C := Sheaf J (Type u)) K
  let _ : HasColimitsOfShape (Discrete (Fin (Fintype.card A))) (Sheaf J (Type u)) :=
    Limits.hasColimitsOfShape_discrete (C := Sheaf J (Type u)) (Fin (Fintype.card A))
  let _ : HasColimitsOfShape (Discrete (Fin (Fintype.card K))) (Sheaf J (Type u)) :=
    Limits.hasColimitsOfShape_discrete (C := Sheaf J (Type u)) (Fin (Fintype.card K))
  let _ : HasColimitsOfShape WalkingParallelPair (Sheaf J (Type u)) :=
    Sheaf.instHasColimitsOfShape
  let eA : Fin (Fintype.card A) ≃ A := (Fintype.equivFin A).symm
  let eK : Fin (Fintype.card K) ≃ K := (Fintype.equivFin K).symm
  let sourceIso :
      (∐ fun j : Fin (Fintype.card K) ↦ h[V (eK j)]^#[J]) ≅
        (∐ fun j : K ↦ h[V j]^#[J]) :=
    Limits.Sigma.reindex eK (fun j : K ↦ h[V j]^#[J])
  let targetIso :
      (∐ fun i : Fin (Fintype.card A) ↦ h[U (eA i)]^#[J]) ≅
        (∐ fun i : A ↦ h[U i]^#[J]) :=
    Limits.Sigma.reindex eA (fun i : A ↦ h[U i]^#[J])
  let left' :
      (∐ fun j : Fin (Fintype.card K) ↦ h[V (eK j)]^#[J]) ⟶
        (∐ fun i : Fin (Fintype.card A) ↦ h[U (eA i)]^#[J]) :=
    sourceIso.hom ≫ left ≫ targetIso.inv
  let right' :
      (∐ fun j : Fin (Fintype.card K) ↦ h[V (eK j)]^#[J]) ⟶
        (∐ fun i : Fin (Fintype.card A) ↦ h[U (eA i)]^#[J]) :=
    sourceIso.hom ≫ right ≫ targetIso.inv
  let pairIso :
      parallelPair left' right' ≅ parallelPair left right :=
    NatIso.ofComponents
      (fun j => by
        cases j with
        | zero => exact sourceIso
        | one => exact targetIso)
      (by
        intro i j f
        cases f <;> simp [left', right'])
  let ecoeq : coequalizer left' right' ≅ coequalizer left right :=
    HasColimit.isoOfNatIso pairIso
  -- Reindex both finite coproducts to `Fin` and transport the identified coequalizer along the
  -- induced parallel-pair isomorphism.
  refine
    ⟨Fintype.card A, Fintype.card K,
      fun i ↦ U (eA i), fun j ↦ V (eK j), left', right', e ≪≫ ecoeq.symm, ?_, ?_⟩
  · intro i
    exact hU (eA i)
  · intro j
    exact hV (eK j)

/-- Helper for Lemma 18.30.7: a morphism from a finite coproduct of basis sheafified
representables into an arbitrary coproduct factors through a finite target coproduct. -/
lemma finiteSourceBasisSheafifiedRepresentableMapFactorsThroughFiniteCoproduct
    {m : ℕ} {V : Fin m → C} (hV : ∀ j, V j ∈ B) {A : Type u} (U : A → C)
    [HasColimitsOfShape (Discrete A) (Sheaf J (Type u))]
    (g : (∐ fun j : Fin m ↦ h[V j]^#[J]) ⟶
      (∐ fun a : A ↦ h[U a]^#[J])) :
    ∃ a : Fin m → A,
      ∃ g' :
        (∐ fun j : Fin m ↦ h[V j]^#[J]) ⟶
          (∐ fun j : Fin m ↦ h[U (a j)]^#[J]),
        g' ≫ Limits.Sigma.desc (fun j : Fin m ↦
          Limits.Sigma.ι (fun b : A ↦ h[U b]^#[J]) (a j)) = g := by
  classical
  -- Factor each source summand through one target summand using quasi-compactness of the basis
  -- object labelling that summand.
  choose a g₁ hg₁ using fun j : Fin m ↦
    basisSheafifiedRepresentableMapFactorsThroughSingleSummand
      (J := J) (B := B) (W := V j) (hW := hV j) (U := U)
      (g := Limits.Sigma.ι (fun k : Fin m ↦ h[V k]^#[J]) j ≫ g)
  let g' :
      (∐ fun j : Fin m ↦ h[V j]^#[J]) ⟶
        (∐ fun j : Fin m ↦ h[U (a j)]^#[J]) :=
    Limits.Sigma.desc (fun j : Fin m ↦
      g₁ j ≫ Limits.Sigma.ι (fun k : Fin m ↦ h[U (a k)]^#[J]) j)
  refine ⟨a, g', ?_⟩
  -- Compare the two maps by restricting to each source summand.
  apply Limits.Sigma.hom_ext
  intro j
  simp only [g', Category.assoc, Limits.Sigma.ι_desc]
  simpa using hg₁ j

/-- Helper for Lemma 18.30.7: two parallel maps from a finite coproduct of basis sheafified
representables into one arbitrary coproduct factor through one common finite target coproduct. -/
lemma finiteParallelPairFactorsThroughCommonFiniteTargetCoproduct
    {m : ℕ} {V : Fin m → C} (hV : ∀ j, V j ∈ B) {A : Type u} (U : A → C)
    [HasColimitsOfShape (Discrete A) (Sheaf J (Type u))]
    (left right : (∐ fun j : Fin m ↦ h[V j]^#[J]) ⟶
      (∐ fun a : A ↦ h[U a]^#[J])) :
    ∃ a : Fin (m + m) → A,
      ∃ left₀ right₀ :
        (∐ fun j : Fin m ↦ h[V j]^#[J]) ⟶
          (∐ fun i : Fin (m + m) ↦ h[U (a i)]^#[J]),
        left₀ ≫ Limits.Sigma.desc (fun i : Fin (m + m) ↦
          Limits.Sigma.ι (fun b : A ↦ h[U b]^#[J]) (a i)) = left ∧
        right₀ ≫ Limits.Sigma.desc (fun i : Fin (m + m) ↦
          Limits.Sigma.ι (fun b : A ↦ h[U b]^#[J]) (a i)) = right := by
  let _ : HasColimitsOfShape (Discrete (Fin (m + m))) (Sheaf J (Type u)) :=
    Limits.hasColimitsOfShape_discrete (C := Sheaf J (Type u)) (Fin (m + m))
  -- Factor each branch separately, then place the two finite targets into one concatenated
  -- coproduct.
  obtain ⟨aLeft, left₁, hleft₁⟩ :=
    finiteSourceBasisSheafifiedRepresentableMapFactorsThroughFiniteCoproduct
      (J := J) (B := B) (hV := hV) (U := U) (g := left)
  obtain ⟨aRight, right₁, hright₁⟩ :=
    finiteSourceBasisSheafifiedRepresentableMapFactorsThroughFiniteCoproduct
      (J := J) (B := B) (hV := hV) (U := U) (g := right)
  let a : Fin (m + m) → A := Fin.append aLeft aRight
  let leftInclusion :
      (∐ fun j : Fin m ↦ h[U (aLeft j)]^#[J]) ⟶
        (∐ fun i : Fin (m + m) ↦ h[U (a i)]^#[J]) :=
    Limits.Sigma.desc (fun j : Fin m ↦
      Limits.Sigma.ι (fun i : Fin (m + m) ↦ h[U (a i)]^#[J]) (Fin.castAdd m j))
  let rightInclusion :
      (∐ fun j : Fin m ↦ h[U (aRight j)]^#[J]) ⟶
        (∐ fun i : Fin (m + m) ↦ h[U (a i)]^#[J]) :=
    Limits.Sigma.desc (fun j : Fin m ↦
      Limits.Sigma.ι (fun i : Fin (m + m) ↦ h[U (a i)]^#[J]) (Fin.natAdd m j))
  let ambientDesc :
      (∐ fun i : Fin (m + m) ↦ h[U (a i)]^#[J]) ⟶
        (∐ fun b : A ↦ h[U b]^#[J]) :=
    Limits.Sigma.desc (fun i : Fin (m + m) ↦
      Limits.Sigma.ι (fun b : A ↦ h[U b]^#[J]) (a i))
  have hleftInclusion :
      leftInclusion ≫ ambientDesc =
        Limits.Sigma.desc (fun j : Fin m ↦
          Limits.Sigma.ι (fun b : A ↦ h[U b]^#[J]) (aLeft j)) := by
    -- The left block of the concatenated finite coproduct lands in the original left factor.
    apply Limits.Sigma.hom_ext
    intro j
    simp [leftInclusion, ambientDesc, a, Fin.append]
  have hrightInclusion :
      rightInclusion ≫ ambientDesc =
        Limits.Sigma.desc (fun j : Fin m ↦
          Limits.Sigma.ι (fun b : A ↦ h[U b]^#[J]) (aRight j)) := by
    -- The right block of the concatenated finite coproduct lands in the original right factor.
    apply Limits.Sigma.hom_ext
    intro j
    simp [rightInclusion, ambientDesc, a, Fin.append]
  refine ⟨a, left₁ ≫ leftInclusion, right₁ ≫ rightInclusion, ?_, ?_⟩
  · -- Postcomposing the left finite factorization with the concatenated inclusion recovers `left`.
    calc
      (left₁ ≫ leftInclusion) ≫ ambientDesc =
          left₁ ≫ Limits.Sigma.desc (fun j : Fin m ↦
            Limits.Sigma.ι (fun b : A ↦ h[U b]^#[J]) (aLeft j)) := by
              rw [Category.assoc, hleftInclusion]
      _ = left := hleft₁
  · -- The same concatenation argument recovers `right`.
    calc
      (right₁ ≫ rightInclusion) ≫ ambientDesc =
          right₁ ≫ Limits.Sigma.desc (fun j : Fin m ↦
            Limits.Sigma.ι (fun b : A ↦ h[U b]^#[J]) (aRight j)) := by
              rw [Category.assoc, hrightInclusion]
      _ = right := hright₁

/-- Helper for Lemma 18.30.7: the product stage category
`Finset (Discrete K) × Finset (Discrete A)` is filtered, with upper bounds given by componentwise
union. -/
lemma isFiltered_finsetProductStages
    (K A : Type u) :
    IsFiltered (Finset (Discrete K) × Finset (Discrete A)) := by
  -- The product index is a preorder category, so it is enough to supply one object, common upper
  -- bounds, and use subsingleton morphisms for the coherence condition.
  refine
    { nonempty := ?_
      cocone_objs := ?_
      cocone_maps := ?_ }
  · exact ⟨(∅, ∅)⟩
  · intro X Y
    refine ⟨(X.1 ∪ Y.1, X.2 ∪ Y.2), ?_, ?_, ?_⟩
    · exact homOfLE ⟨le_sup_left, le_sup_left⟩
    · exact homOfLE ⟨le_sup_right, le_sup_right⟩
    · exact Subsingleton.elim _ _
  · intro X Y f g
    exact ⟨Y, 𝟙 Y, Subsingleton.elim _ _⟩

/-- Helper for Lemma 18.30.7: the first projection from product finite-support stages to the
source-support index is final. -/
lemma finsetProductFst_final
    {K A : Type u} :
    Functor.Final
      (Prod.fst : (Finset (Discrete K) × Finset (Discrete A)) ⥤ Finset (Discrete K)) := by
  let I : Type u := Finset (Discrete K) × Finset (Discrete A)
  haveI : IsFiltered I := isFiltered_finsetProductStages (K := K) (A := A)
  -- Every source stage occurs as the first component of a product stage, and the codomain is
  -- thin, so the equalizer condition is automatic.
  refine Functor.final_of_exists_of_isFiltered
    (Prod.fst : I ⥤ Finset (Discrete K)) ?_ ?_
  · intro s
    exact ⟨(s, ∅), ⟨𝟙 s⟩⟩
  · intro d c s s'
    exact ⟨c, 𝟙 _, Subsingleton.elim _ _⟩

/-- Helper for Lemma 18.30.7: from a support function `supp`, the product stage index maps to the
target-support index by adjoining free finite target padding. -/
def finsetSupportAugmentFunctor
    {K A : Type u}
    (supp : Finset (Discrete K) → Finset (Discrete A))
    (hsupp_mono : Monotone supp) :
    (Finset (Discrete K) × Finset (Discrete A)) ⥤ Finset (Discrete A) where
  obj p := supp p.1 ∪ p.2
  map h := homOfLE <| sup_le_sup (hsupp_mono (leOfHom h).1) (leOfHom h).2

/-- Helper for Lemma 18.30.7: the augmentation functor `(s, t) ↦ supp s ∪ t` is final whenever
`supp` is monotone and sends the empty set to the empty set. -/
lemma finsetSupportAugment_final
    {K A : Type u}
    (supp : Finset (Discrete K) → Finset (Discrete A))
    (hsupp_mono : Monotone supp)
    (hsupp_empty : supp ∅ = ∅) :
    Functor.Final (finsetSupportAugmentFunctor supp hsupp_mono) := by
  let I : Type u := Finset (Discrete K) × Finset (Discrete A)
  haveI : IsFiltered I := isFiltered_finsetProductStages (K := K) (A := A)
  -- Any finite target stage is already hit by the empty-source stage with that padding, and the
  -- codomain is thin so parallel morphisms equalize automatically.
  refine Functor.final_of_exists_of_isFiltered
    (finsetSupportAugmentFunctor supp hsupp_mono) ?_ ?_
  · intro t
    refine ⟨(∅, t), ?_⟩
    refine ⟨homOfLE ?_⟩
    simpa [finsetSupportAugmentFunctor, hsupp_empty] using
      (le_sup_right : t ≤ supp ∅ ∪ t)
  · intro d c s s'
    exact ⟨c, 𝟙 _, Subsingleton.elim _ _⟩

/-- Helper for Lemma 18.30.7: if a finite-support target selector sends unions into unions, then
support-closed finite source/target pairs form a filtered thin category. -/
lemma isFiltered_supportPairStages
    {K A : Type u}
    (supp : Finset (Discrete K) → Finset (Discrete A))
    (hsupp_union :
      ∀ s₁ s₂ : Finset (Discrete K), supp (s₁ ∪ s₂) ≤ supp s₁ ∪ supp s₂) :
    IsFiltered { p : Finset (Discrete K) × Finset (Discrete A) // supp p.1 ≤ p.2 } := by
  -- The index is a preorder category, so it is enough to supply one object, common upper bounds,
  -- and use subsingleton morphisms for parallel-map compatibility.
  refine
    { nonempty := ?_
      cocone_objs := ?_
      cocone_maps := ?_ }
  · exact ⟨⟨(∅, supp ∅), le_rfl⟩⟩
  · intro X Y
    refine ⟨⟨(X.1.1 ∪ Y.1.1, X.1.2 ∪ Y.1.2), ?_⟩, ?_, ?_, ?_⟩
    · exact le_trans (hsupp_union _ _) (sup_le_sup X.2 Y.2)
    · exact homOfLE (show X.1 ≤ (X.1.1 ∪ Y.1.1, X.1.2 ∪ Y.1.2) by
        exact ⟨le_sup_left, le_sup_left⟩)
    · exact homOfLE (show Y.1 ≤ (X.1.1 ∪ Y.1.1, X.1.2 ∪ Y.1.2) by
        exact ⟨le_sup_right, le_sup_right⟩)
    · exact Subsingleton.elim _ _
  · intro X Y f g
    exact ⟨Y, 𝟙 Y, Subsingleton.elim _ _⟩

/-- Helper for Lemma 18.30.7: the finite-union support selector built from component supports sends
unions of source supports into unions of target supports. -/
lemma supportOfComponents_union_le
    {K A : Type u} (componentSupport : K → Finset (Discrete A))
    (s₁ s₂ : Finset (Discrete K)) :
    (s₁ ∪ s₂).biUnion (fun b ↦ componentSupport b.as) ≤
      s₁.biUnion (fun b ↦ componentSupport b.as) ∪
        s₂.biUnion (fun b ↦ componentSupport b.as) := by
  intro a ha
  -- Split according to whether the witnessing source component lies in the left or right union.
  rcases Finset.mem_biUnion.mp ha with ⟨b, hb, hba⟩
  rcases Finset.mem_union.mp hb with hb | hb
  · exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_biUnion.mpr ⟨b, hb, hba⟩
  · exact Finset.mem_union.mpr <| Or.inr <| Finset.mem_biUnion.mpr ⟨b, hb, hba⟩

/-- Helper for Lemma 18.30.7: the support selector built from component supports is monotone in
the finite source support. -/
lemma supportOfComponents_mono
    {K A : Type u} (componentSupport : K → Finset (Discrete A)) :
    Monotone (fun s : Finset (Discrete K) ↦ s.biUnion (fun b ↦ componentSupport b.as)) := by
  intro s t hst a ha
  -- Move the witness for membership in the smaller biunion across the source-support inclusion.
  rcases Finset.mem_biUnion.mp ha with ⟨b, hb, hba⟩
  exact Finset.mem_biUnion.mpr ⟨b, hst hb, hba⟩

/-- Helper for Lemma 18.30.7: the support selector built from component supports vanishes on the
empty finite source support. -/
lemma supportOfComponents_empty
    {K A : Type u} (componentSupport : K → Finset (Discrete A)) :
    (∅ : Finset (Discrete K)).biUnion (fun b ↦ componentSupport b.as) = ∅ := by
  -- The empty source support contributes no target indices.
  simp

/-- Helper for Lemma 18.30.7: if a source component lies in a finite source support, then its
chosen target support lies in the associated biunion support. -/
private theorem componentSupport_le_supportOf_mem
    {K A : Type u} (componentSupport : K → Finset (Discrete A))
    {j : K} {s : Finset (Discrete K)} (hj : (Discrete.mk j) ∈ s) :
    componentSupport j ≤ s.biUnion (fun b ↦ componentSupport b.as) := by
  intro a ha
  exact Finset.mem_biUnion.mpr ⟨Discrete.mk j, hj, ha⟩

/-- Helper for Lemma 18.30.7: support-closed finite source/target pairs for a support selector. -/
abbrev supportPairIndex
    {K A : Type u} (supp : Finset (Discrete K) → Finset (Discrete A)) :=
  { p : Finset (Discrete K) × Finset (Discrete A) // supp p.1 ≤ p.2 }

/-- Helper for Lemma 18.30.7: the source projection from support-closed pairs forgets the target
support and remembers only the finite source support. -/
def supportPairSourceProjection
    {K A : Type u} (supp : Finset (Discrete K) → Finset (Discrete A)) :
    supportPairIndex supp ⥤ Finset (Discrete K) where
  obj p := p.1.1
  map {p q} f := homOfLE (show p.1.1 ≤ q.1.1 from (leOfHom f).1)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- Helper for Lemma 18.30.7: the target projection from support-closed pairs forgets the source
support and remembers only the finite target support. -/
def supportPairTargetProjection
    {K A : Type u} (supp : Finset (Discrete K) → Finset (Discrete A)) :
    supportPairIndex supp ⥤ Finset (Discrete A) where
  obj p := p.1.2
  map {p q} f := homOfLE (show p.1.2 ≤ q.1.2 from (leOfHom f).2)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- Helper for Lemma 18.30.7: the source projection from support-closed pairs is final because it
is right adjoint to the graph embedding `s ↦ (s, supp s)`. -/
lemma supportPairSourceProjection_final
    {K A : Type u} (supp : Finset (Discrete K) → Finset (Discrete A))
    (hsupp_mono : Monotone supp) :
    Functor.Final (supportPairSourceProjection supp) := by
  let lift : Finset (Discrete K) ⥤ supportPairIndex supp where
    obj s := ⟨(s, supp s), le_rfl⟩
    map {s t} f := homOfLE <| show (s, supp s) ≤ (t, supp t) from
      ⟨leOfHom f, hsupp_mono (leOfHom f)⟩
    map_id _ := Subsingleton.elim _ _
    map_comp _ _ := Subsingleton.elim _ _
  let adj : lift ⊣ supportPairSourceProjection supp :=
    Adjunction.mkOfHomEquiv
      { homEquiv := fun s p =>
          { toFun := fun f => homOfLE <| show (s, supp s) ≤ p.1 from
              ⟨leOfHom f, le_trans (hsupp_mono (leOfHom f)) p.2⟩
            invFun := fun f => homOfLE <| show s ≤ p.1.1 from (leOfHom f).1
            left_inv := fun _ => Subsingleton.elim _ _
            right_inv := fun _ => Subsingleton.elim _ _ }
        homEquiv_naturality_left_symm := by
          intro s₁ s₂ p f g
          exact Subsingleton.elim _ _
        homEquiv_naturality_right := by
          intro s p q f g
          exact Subsingleton.elim _ _ }
  -- Right adjoints are final, so the projection inherits finality from the adjunction.
  exact Functor.final_of_adjunction adj

/-- Helper for Lemma 18.30.7: the target projection from support-closed pairs is final because it
is right adjoint to the constant-empty-source embedding `t ↦ (∅, t)`. -/
lemma supportPairTargetProjection_final
    {K A : Type u} (supp : Finset (Discrete K) → Finset (Discrete A))
    (hsupp_empty : supp ∅ = ∅) :
    Functor.Final (supportPairTargetProjection supp) := by
  let lift : Finset (Discrete A) ⥤ supportPairIndex supp where
    obj t := ⟨(∅, t), by
      simpa [hsupp_empty] using (show (∅ : Finset (Discrete A)) ≤ t from bot_le)⟩
    map {s t} f := homOfLE <| show (∅, s) ≤ (∅, t) from
      ⟨show (∅ : Finset (Discrete K)) ≤ ∅ from le_rfl, leOfHom f⟩
    map_id _ := Subsingleton.elim _ _
    map_comp _ _ := Subsingleton.elim _ _
  let adj : lift ⊣ supportPairTargetProjection supp :=
    Adjunction.mkOfHomEquiv
      { homEquiv := fun s p =>
          { toFun := fun f => homOfLE <| show s ≤ p.1.2 from (leOfHom f).2
            invFun := fun f => homOfLE <| show (∅, s) ≤ p.1 from
              ⟨show (∅ : Finset (Discrete K)) ≤ p.1.1 from bot_le, leOfHom f⟩
            left_inv := fun _ => Subsingleton.elim _ _
            right_inv := fun _ => Subsingleton.elim _ _ }
        homEquiv_naturality_left_symm := by
          intro s₁ s₂ p f g
          exact Subsingleton.elim _ _
        homEquiv_naturality_right := by
          intro s p q f g
          exact Subsingleton.elim _ _ }
  -- Again, finality is the standard right-adjoint consequence rather than a bespoke comma proof.
  exact Functor.final_of_adjunction adj

local instance (ι : Type u) : HasColimitsOfShape (Finset (Discrete ι)) (Sheaf J (Type u)) := by
  -- The sheaf category already has all small colimits, so finite-support index categories are
  -- available automatically.
  exact Sheaf.instHasColimitsOfShape

/-- Helper for Lemma 18.30.7: the full coproduct of a family of sheaves is the colimit of its
finite-subcoproduct diagram indexed by `Finset (Discrete ι)`. -/
noncomputable def finiteSubcoproductsSheafCoconeIsColimit
    {ι : Type u} (F : ι → Sheaf J (Type u)) :
    IsColimit (finiteSubcoproductsCocone F) := by
  -- This is the generic finite-subcoproduct colimit construction specialized to sheaves.
  exact isColimitFiniteSubproductsCocone F

/-- Helper for Lemma 18.30.7: the colimit of the finite-subcoproduct sheaf diagram is canonically
the ambient coproduct sheaf. -/
noncomputable def finiteSubcoproductsSheafColimitIso
    {ι : Type u} (F : ι → Sheaf J (Type u)) :
    ∐ F ≅ colimit (liftToFinsetObj (Discrete.functor F)) := by
  -- Compare the standard finite-subcoproduct cocone with the ambient coproduct cocone.
  exact (finiteSubcoproductsSheafCoconeIsColimit (J := J) F).coconePointUniqueUpToIso
    (colimit.isColimit (liftToFinsetObj (Discrete.functor F)))

/-- Helper for Lemma 18.30.7: the `hom` of the finite-subcoproduct colimit isomorphism sends the
explicit finite-stage coproduct inclusion to the corresponding colimit leg. -/
lemma finiteSubcoproductsSheafColimitIso_hom_app
    {ι : Type u} (F : ι → Sheaf J (Type u)) (s : Finset (Discrete ι)) :
    Limits.Sigma.desc (fun i : s ↦ Limits.Sigma.ι F i.1.as) ≫
        (finiteSubcoproductsSheafColimitIso (J := J) F).hom =
      colimit.ι (liftToFinsetObj (Discrete.functor F)) s := by
  -- Proof comment: compare the two colimit cocones at the finite stage `s`, then normalize the
  -- source cocone leg to the explicit finite-subcoproduct inclusion.
  rw [show Limits.Sigma.desc (fun i : s ↦ Limits.Sigma.ι F i.1.as) =
      (finiteSubcoproductsCocone F).ι.app s by
      rw [finiteSubcoproductsCocone_ι_app]]
  simpa [finiteSubcoproductsSheafColimitIso] using
    (IsColimit.comp_coconePointUniqueUpToIso_hom
      (finiteSubcoproductsSheafCoconeIsColimit (J := J) F)
      (colimit.isColimit (liftToFinsetObj (Discrete.functor F)))
      s)

/-- Helper for Lemma 18.30.7: both arrows contributed by one source summand of the infinite
parallel pair factor through a common finite target subcoproduct. -/
lemma basisSheafifiedRepresentableParallelPairFactorsThroughFiniteSubcoproduct
    {A K : Type u} (U : A → C) (V : K → C)
    (hV : ∀ j, V j ∈ B)
    (left right :
      (∐ fun j : K ↦ h[V j]^#[J]) ⟶
        (∐ fun i : A ↦ h[U i]^#[J]))
    (j : K) :
    ∃ t : Finset (Discrete A),
      ∃ left₀ right₀ :
        h[V j]^#[J] ⟶
          (liftToFinsetObj (Discrete.functor (fun i : A ↦ h[U i]^#[J]))).obj t,
        left₀ ≫ ((finiteSubcoproductsCocone (fun i : A ↦ h[U i]^#[J])).ι.app t) =
            Limits.Sigma.ι (fun b : K ↦ h[V b]^#[J]) j ≫ left ∧
          right₀ ≫ ((finiteSubcoproductsCocone (fun i : A ↦ h[U i]^#[J])).ι.app t) =
            Limits.Sigma.ι (fun b : K ↦ h[V b]^#[J]) j ≫ right := by
  classical
  let F : A → Sheaf J (Type u) := fun i ↦ h[U i]^#[J]
  let D : Finset (Discrete A) ⥤ Sheaf J (Type u) := liftToFinsetObj (Discrete.functor F)
  -- Factor the two branches through single target summands and then enlarge to one common finite
  -- support containing both chosen targets.
  obtain ⟨iLeft, left₁, hleft₁⟩ :=
    basisSheafifiedRepresentableMapFactorsThroughSingleSummand
      (J := J) (B := B) (W := V j) (hW := hV j) (U := U)
      (g := Limits.Sigma.ι (fun b : K ↦ h[V b]^#[J]) j ≫ left)
  obtain ⟨iRight, right₁, hright₁⟩ :=
    basisSheafifiedRepresentableMapFactorsThroughSingleSummand
      (J := J) (B := B) (W := V j) (hW := hV j) (U := U)
      (g := Limits.Sigma.ι (fun b : K ↦ h[V b]^#[J]) j ≫ right)
  let t : Finset (Discrete A) := {⟨iLeft⟩, ⟨iRight⟩}
  let leftIdx : t := ⟨⟨iLeft⟩, by simp [t]⟩
  let rightIdx : t := ⟨⟨iRight⟩, by simp [t]⟩
  let left₀ : h[V j]^#[J] ⟶ D.obj t :=
    left₁ ≫ Limits.Sigma.ι (fun i : t ↦ h[U i.1.as]^#[J]) leftIdx
  let right₀ : h[V j]^#[J] ⟶ D.obj t :=
    right₁ ≫ Limits.Sigma.ι (fun i : t ↦ h[U i.1.as]^#[J]) rightIdx
  refine ⟨t, left₀, right₀, ?_⟩
  constructor
  · -- The left factorization becomes the original branch after expanding the finite-subcoproduct
    -- inclusion at the chosen target index.
    calc
      left₀ ≫ ((finiteSubcoproductsCocone F).ι.app t) =
          left₁ ≫ Limits.Sigma.ι F iLeft := by
            simp [left₀, D, F, t, leftIdx, Category.assoc, finiteSubcoproductsCocone_ι_app]
      _ = Limits.Sigma.ι (fun b : K ↦ h[V b]^#[J]) j ≫ left := hleft₁
  · -- The right branch is identical after replacing the chosen target index.
    calc
      right₀ ≫ ((finiteSubcoproductsCocone F).ι.app t) =
          right₁ ≫ Limits.Sigma.ι F iRight := by
            simp [right₀, D, F, t, rightIdx, Category.assoc, finiteSubcoproductsCocone_ι_app]
      _ = Limits.Sigma.ι (fun b : K ↦ h[V b]^#[J]) j ≫ right := hright₁

/-- Helper for Lemma 18.30.7: a chosen finite factorization of one source summand of the infinite
parallel pair can be enlarged along any bigger finite target support. -/
lemma basisSheafifiedRepresentableParallelPairFactorsThroughTargetStage
    {A K : Type u} (U : A → C) (V : K → C)
    (hV : ∀ j, V j ∈ B)
    (left right :
      (∐ fun j : K ↦ h[V j]^#[J]) ⟶
        (∐ fun i : A ↦ h[U i]^#[J]))
    (j : K) (t : Finset (Discrete A))
    (ht : (Classical.choose
      (basisSheafifiedRepresentableParallelPairFactorsThroughFiniteSubcoproduct
        (J := J) (B := B) U V hV left right j)) ≤ t) :
    ∃ leftₜ rightₜ :
        h[V j]^#[J] ⟶
          (liftToFinsetObj (Discrete.functor (fun i : A ↦ h[U i]^#[J]))).obj t,
      leftₜ ≫ ((finiteSubcoproductsCocone (fun i : A ↦ h[U i]^#[J])).ι.app t) =
          Limits.Sigma.ι (fun b : K ↦ h[V b]^#[J]) j ≫ left ∧
        rightₜ ≫ ((finiteSubcoproductsCocone (fun i : A ↦ h[U i]^#[J])).ι.app t) =
          Limits.Sigma.ι (fun b : K ↦ h[V b]^#[J]) j ≫ right := by
  classical
  let F : A → Sheaf J (Type u) := fun i ↦ h[U i]^#[J]
  let D : Finset (Discrete A) ⥤ Sheaf J (Type u) := liftToFinsetObj (Discrete.functor F)
  let s : Finset (Discrete A) := Classical.choose
    (basisSheafifiedRepresentableParallelPairFactorsThroughFiniteSubcoproduct
      (J := J) (B := B) U V hV left right j)
  let left₀ :
      h[V j]^#[J] ⟶ D.obj s :=
    Classical.choose <|
      Classical.choose <|
        basisSheafifiedRepresentableParallelPairFactorsThroughFiniteSubcoproduct
          (J := J) (B := B) U V hV left right j
  let right₀ :
      h[V j]^#[J] ⟶ D.obj s :=
    Classical.choose <|
      Classical.choose <|
        Classical.choose <|
          basisSheafifiedRepresentableParallelPairFactorsThroughFiniteSubcoproduct
            (J := J) (B := B) U V hV left right j
  have hleft₀ :
      left₀ ≫ ((finiteSubcoproductsCocone F).ι.app s) =
        Limits.Sigma.ι (fun b : K ↦ h[V b]^#[J]) j ≫ left := by
    -- Unpack the chosen finite factorization and keep only the left branch identity.
    exact (Classical.choose <|
      Classical.choose <|
        Classical.choose <|
          basisSheafifiedRepresentableParallelPairFactorsThroughFiniteSubcoproduct
            (J := J) (B := B) U V hV left right j).1
  have hright₀ :
      right₀ ≫ ((finiteSubcoproductsCocone F).ι.app s) =
        Limits.Sigma.ι (fun b : K ↦ h[V b]^#[J]) j ≫ right := by
    -- The right branch is the second component of the same chosen finite factorization.
    exact (Classical.choose <|
      Classical.choose <|
        Classical.choose <|
          basisSheafifiedRepresentableParallelPairFactorsThroughFiniteSubcoproduct
            (J := J) (B := B) U V hV left right j).2
  refine ⟨left₀ ≫ D.map (homOfLE ht), right₀ ≫ D.map (homOfLE ht), ?_, ?_⟩
  · -- Postcompose the chosen factorization with the canonical enlargement map into the bigger
    -- target support.
    calc
      (left₀ ≫ D.map (homOfLE ht)) ≫ ((finiteSubcoproductsCocone F).ι.app t) =
          left₀ ≫ ((finiteSubcoproductsCocone F).ι.app s) := by
            rw [Category.assoc, (finiteSubcoproductsCocone F).w (homOfLE ht)]
      _ = Limits.Sigma.ι (fun b : K ↦ h[V b]^#[J]) j ≫ left := hleft₀
  · -- The right factorization enlarges in the same way.
    calc
      (right₀ ≫ D.map (homOfLE ht)) ≫ ((finiteSubcoproductsCocone F).ι.app t) =
          right₀ ≫ ((finiteSubcoproductsCocone F).ι.app s) := by
            rw [Category.assoc, (finiteSubcoproductsCocone F).w (homOfLE ht)]
      _ = Limits.Sigma.ι (fun b : K ↦ h[V b]^#[J]) j ≫ right := hright₀

/-- Helper for Lemma 18.30.7: a support-closed finite stage already has a finite basis coequalizer
presentation once its two finite arrows are fixed. -/
private theorem hasFiniteBasisSheafifiedRepresentableCoequalizerPresentation_of_supportPairStage
    {X : Sheaf J (Type u)} {A K : Type u}
    (U : A → C) (V : K → C)
    (hU : ∀ i, U i ∈ B) (hV : ∀ j, V j ∈ B)
    {supp : Finset (Discrete K) → Finset (Discrete A)}
    (p : supportPairIndex supp)
    (left right :
      (∐ fun j : p.1.1 ↦ h[V j.1.as]^#[J]) ⟶
        (∐ fun i : p.1.2 ↦ h[U i.1.as]^#[J]))
    (e : X ≅ coequalizer left right) :
    HasFiniteBasisSheafifiedRepresentableCoequalizerPresentation J B X := by
  classical
  -- Reindex the stage along the finite subtype carriers supplied by the two supports.
  exact hasFiniteBasisSheafifiedRepresentableCoequalizerPresentation_of_finiteTypes
    (J := J) (B := B)
    (U := fun i : p.1.2 ↦ U i.1.as) (V := fun j : p.1.1 ↦ V j.1.as)
    left right e
    (fun i ↦ hU i.1.as)
    (fun j ↦ hV j.1.as)

-- Proof sketch: first use Lemma `18.30.6` in Situation `18.30.5` to write `ℱ` as the
-- coequalizer of a pair of maps between possibly infinite coproducts of basis sheafified
-- representables. Then use quasi-compactness of basis objects together with the finite-subcoproduct
-- argument from Lemma `7.17.7` to express that coequalizer as a filtered colimit over finite
-- subdiagrams.
/-- Lemma 18.30.7 (1): in Situation `18.30.5`, every sheaf of sets is a filtered colimit of
sheaves admitting finite coequalizer presentations by sheafified representables `h_U^#` with
`U ∈ B`. -/
theorem exists_filteredColimitPresentation_by_finite_basis_sheafifiedRepresentable_coequalizers
    (ℱ : Sheaf J (Type u)) :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I)
      (pres : ColimitPresentation I ℱ),
        ∀ i, HasFiniteBasisSheafifiedRepresentableCoequalizerPresentation J B (pres.diag.obj i) :=
by
  -- Route correction: first normalize `ℱ` to the explicit infinite coequalizer presentation
  -- already available in this file before attempting any finite-stage cutdown.
  classical
  obtain ⟨A, K, U, V, left, right, e, hU, hV⟩ :=
    existsBasisSheafifiedRepresentableInfiniteCoequalizerPresentation
      (J := J) (B := B) ℱ
  choose componentSupport left₀ right₀ hleft₀ hright₀ using
    fun j : K ↦
      basisSheafifiedRepresentableParallelPairFactorsThroughFiniteSubcoproduct
        (J := J) (B := B) U V hV left right j
  let supp : Finset (Discrete K) → Finset (Discrete A) :=
    fun s ↦ s.biUnion (fun j ↦ componentSupport j.as)
  have hsupp_union :
      ∀ s₁ s₂ : Finset (Discrete K), supp (s₁ ∪ s₂) ≤ supp s₁ ∪ supp s₂ := by
    intro s₁ s₂
    simpa [supp] using supportOfComponents_union_le componentSupport s₁ s₂
  have hsupp_mono : Monotone supp := by
    simpa [supp] using supportOfComponents_mono componentSupport
  have hsupp_empty : supp ∅ = ∅ := by
    simpa [supp] using supportOfComponents_empty componentSupport
  let I : Type u := supportPairIndex supp
  let _ : IsFiltered I := isFiltered_supportPairStages supp hsupp_union
  let sourceF : K → Sheaf J (Type u) := fun j ↦ h[V j]^#[J]
  let targetF : A → Sheaf J (Type u) := fun i ↦ h[U i]^#[J]
  let sourceDiag : Finset (Discrete K) ⥤ Sheaf J (Type u) :=
    liftToFinsetObj (Discrete.functor sourceF)
  let targetDiag : Finset (Discrete A) ⥤ Sheaf J (Type u) :=
    liftToFinsetObj (Discrete.functor targetF)
  have hcomponent_le_target :
      ∀ (p : I) (j : p.1.1), componentSupport j.1.as ≤ p.1.2 := by
    intro p j
    exact le_trans
      (componentSupport_le_supportOf_mem componentSupport j.2)
      p.2
  let leftStage : (p : I) →
      (∐ fun j : p.1.1 ↦ h[V j.1.as]^#[J]) ⟶
        (∐ fun i : p.1.2 ↦ h[U i.1.as]^#[J]) :=
    fun p ↦
      Limits.Sigma.desc fun j : p.1.1 ↦
        Classical.choose <|
          basisSheafifiedRepresentableParallelPairFactorsThroughTargetStage
            (J := J) (B := B) U V hV left right j.1.as p.1.2
            (hcomponent_le_target p j)
  let rightStage : (p : I) →
      (∐ fun j : p.1.1 ↦ h[V j.1.as]^#[J]) ⟶
        (∐ fun i : p.1.2 ↦ h[U i.1.as]^#[J]) :=
    fun p ↦
      Limits.Sigma.desc fun j : p.1.1 ↦
        Classical.choose <|
          Classical.choose <|
            basisSheafifiedRepresentableParallelPairFactorsThroughTargetStage
              (J := J) (B := B) U V hV left right j.1.as p.1.2
              (hcomponent_le_target p j)
  have leftStage_fac :
      ∀ (p : I) (j : p.1.1),
        Limits.Sigma.ι (fun b : p.1.1 ↦ h[V b.1.as]^#[J]) j ≫ leftStage p ≫
            ((finiteSubcoproductsCocone targetF).ι.app p.1.2) =
          Limits.Sigma.ι sourceF j.1.as ≫ left := by
    intro p j
    dsimp [leftStage]
    simp [basisSheafifiedRepresentableParallelPairFactorsThroughTargetStage, targetDiag,
      sourceF, targetF, Category.assoc]
  have rightStage_fac :
      ∀ (p : I) (j : p.1.1),
        Limits.Sigma.ι (fun b : p.1.1 ↦ h[V b.1.as]^#[J]) j ≫ rightStage p ≫
            ((finiteSubcoproductsCocone targetF).ι.app p.1.2) =
          Limits.Sigma.ι sourceF j.1.as ≫ right := by
    intro p j
    dsimp [rightStage]
    simp [basisSheafifiedRepresentableParallelPairFactorsThroughTargetStage, targetDiag,
      sourceF, targetF, Category.assoc]
  have leftStage_naturality :
      ∀ {p q : I} (f : p ⟶ q),
        leftStage p ≫
            targetDiag.map (homOfLE (show p.1.2 ≤ q.1.2 from (leOfHom f).2)) =
          sourceDiag.map (homOfLE (show p.1.1 ≤ q.1.1 from (leOfHom f).1)) ≫
            leftStage q := by
    intro p q f
    apply Limits.Sigma.hom_ext
    intro j
    dsimp [leftStage, sourceDiag, targetDiag]
    simp [basisSheafifiedRepresentableParallelPairFactorsThroughTargetStage, Category.assoc]
  have rightStage_naturality :
      ∀ {p q : I} (f : p ⟶ q),
        rightStage p ≫
            targetDiag.map (homOfLE (show p.1.2 ≤ q.1.2 from (leOfHom f).2)) =
          sourceDiag.map (homOfLE (show p.1.1 ≤ q.1.1 from (leOfHom f).1)) ≫
            rightStage q := by
    intro p q f
    apply Limits.Sigma.hom_ext
    intro j
    dsimp [rightStage, sourceDiag, targetDiag]
    simp [basisSheafifiedRepresentableParallelPairFactorsThroughTargetStage, Category.assoc]
  let D : I ⥤ WalkingParallelPair ⥤ Sheaf J (Type u) := by
    refine
      { obj := fun p ↦ parallelPair (leftStage p) (rightStage p)
        map := fun {p q} f ↦
          { app := fun z ↦ match z with
              | WalkingParallelPair.zero =>
                  sourceDiag.map (homOfLE (show p.1.1 ≤ q.1.1 from (leOfHom f).1))
              | WalkingParallelPair.one =>
                  targetDiag.map (homOfLE (show p.1.2 ≤ q.1.2 from (leOfHom f).2))
            naturality := by
              intro z z' g
              cases g
              · simp
              · simpa using leftStage_naturality f
              · simpa using rightStage_naturality f }
        map_id := by
          intro p
          ext z
          cases z <;> simp [sourceDiag, targetDiag]
        map_comp := by
          intro p q r f g
          ext z
          cases z <;> simp [sourceDiag, targetDiag] }
  let c : Cocone D := by
    refine
      { pt := parallelPair left right
        ι :=
          { app := fun p ↦
              { app := fun z ↦ match z with
                  | WalkingParallelPair.zero =>
                      ((finiteSubcoproductsCocone sourceF).ι.app p.1.1)
                  | WalkingParallelPair.one =>
                      ((finiteSubcoproductsCocone targetF).ι.app p.1.2)
                naturality := by
                  intro z z' g
                  cases g
                  · simp
                  · apply Limits.Sigma.hom_ext
                    intro j
                    simpa [sourceF, targetF, Category.assoc] using leftStage_fac p j
                  · apply Limits.Sigma.hom_ext
                    intro j
                    simpa [sourceF, targetF, Category.assoc] using rightStage_fac p j }
            naturality := by
              intro p q f
              ext z
              cases z <;> simp [sourceDiag, targetDiag] } }
  let _ : Functor.Final (supportPairSourceProjection supp) :=
    supportPairSourceProjection_final supp hsupp_mono
  let _ : Functor.Final (supportPairTargetProjection supp) :=
    supportPairTargetProjection_final supp hsupp_empty
  have hzero :
      IsColimit (((evaluation _ _).obj WalkingParallelPair.zero).mapCocone c) := by
    exact
      (Functor.Final.isColimitWhiskerEquiv (supportPairSourceProjection supp)
        (finiteSubcoproductsCocone sourceF)).symm
        (finiteSubcoproductsSheafCoconeIsColimit (J := J) sourceF)
  have hone :
      IsColimit (((evaluation _ _).obj WalkingParallelPair.one).mapCocone c) := by
    exact
      (Functor.Final.isColimitWhiskerEquiv (supportPairTargetProjection supp)
        (finiteSubcoproductsCocone targetF)).symm
        (finiteSubcoproductsSheafCoconeIsColimit (J := J) targetF)
  have hc : IsColimit c := by
    -- Proof comment: colimits in the functor category over `WalkingParallelPair` are detected
    -- endpointwise, so the two finite-subcoproduct computations close the categorical core.
    refine evaluationJointlyReflectsColimits c ?_
    intro z
    cases z
    · simpa [D, c, sourceDiag, supportPairSourceProjection]
        using hzero
    · simpa [D, c, targetDiag, supportPairTargetProjection]
        using hone
  let pres : ColimitPresentation I ℱ :=
    { diag := D ⋙ colim
      ι :=
        { app := fun p ↦ (colim.mapCocone c).ι.app p ≫ e.inv
          naturality := by
            intro p q f
            simpa [Category.assoc] using
              congrArg (fun k ↦ k ≫ e.inv) ((colim.mapCocone c).ι.naturality f) }
      isColimit := by
        have hcolim : IsColimit (colim.mapCocone c) :=
          isColimitOfPreserves colim hc
        refine IsColimit.ofIsoColimit hcolim ?_
        refine Cocone.ext e ?_
        intro p
        simp }
  refine ⟨I, inferInstance, inferInstance, pres, ?_⟩
  intro p
  -- Proof comment: each stage object is by construction the coequalizer of a parallel pair on
  -- finite source and target supports, so it satisfies the public finite-presentation predicate.
  simpa [pres, D] using
    hasFiniteBasisSheafifiedRepresentableCoequalizerPresentation_of_supportPairStage
      (J := J) (B := B) U V hU hV p (leftStage p) (rightStage p) (Iso.refl _)

end CategoryTheory.GrothendieckTopology

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]
variable (𝒪 : Sheaf J CommRingCat.{u}) (B : Set C)
variable [J.HasQuasiCompactBasisWithQuasiCompactFiberProducts B]

/-- An `\mathcal O`-module has a finite basis cokernel presentation if it is isomorphic to the
cokernel of a map between finite coproducts of the extensions by zero `j_{U!}\mathcal O_U` built
from objects of `B`. -/
abbrev HasFiniteBasisConstructibleModuleCokernelPresentation
    (ℱ : SheafOfModules (ringSheaf J 𝒪)) : Prop :=
  ∃ (n m : ℕ) (U : Fin n → C) (V : Fin m → C),
    ∃ (f :
      (∐ fun j : Fin m ↦ localizedStructureModuleExtensionByZero 𝒪 (V j)) ⟶
        (∐ fun i : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)))
      (_ : ℱ ≅ cokernel f),
        (∀ i, U i ∈ B) ∧
          ∀ j, V j ∈ B

/-- Helper for Lemma 18.30.7: every module admits a two-step basis presentation by an epimorphism
from a coproduct of `j_{U!}\mathcal O_U` and an epimorphism onto its kernel from another such
coproduct. -/
lemma existsBasisConstructibleModuleKernelPresentation
    (ℱ : SheafOfModules (ringSheaf J 𝒪)) :
    ∃ (A K : Type u) (U : A → C) (V : K → C)
      (φ :
        (∐ fun i : A ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)) ⟶ ℱ)
      (ψ :
        (∐ fun j : K ↦ localizedStructureModuleExtensionByZero 𝒪 (V j)) ⟶ kernel φ),
        Epi φ ∧ Epi ψ ∧
          (∀ i, U i ∈ B) ∧
            ∀ j, V j ∈ B := by
  -- First choose the epimorphic basis-coproduct presentation of `ℱ`.
  obtain ⟨A, U, hU, φ, hφ⟩ :=
    exists_epi_from_coproduct_basis_localizedStructureModuleExtensionByZero
      (𝒪 := 𝒪) B ℱ
  -- Then apply the same result to the kernel of that epimorphism.
  obtain ⟨K, V, hV, ψ, hψ⟩ :=
    exists_epi_from_coproduct_basis_localizedStructureModuleExtensionByZero
      (𝒪 := 𝒪) B (kernel φ)
  exact ⟨A, K, U, V, φ, ψ, hφ, hψ, hU, hV⟩

/-- Helper for Lemma 18.30.7: a one-stage module diagram gives a degenerate filtered colimit
presentation. -/
lemma exists_filteredColimitPresentation_of_hasFiniteBasisConstructibleModuleCokernelPresentation
    (ℱ : SheafOfModules (ringSheaf J 𝒪))
    (hℱ : HasFiniteBasisConstructibleModuleCokernelPresentation 𝒪 B ℱ) :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I)
      (pres : ColimitPresentation I ℱ),
        ∀ i, HasFiniteBasisConstructibleModuleCokernelPresentation 𝒪 B (pres.diag.obj i) := by
  let I : Type u := Discrete (ULift PUnit)
  let pres : ColimitPresentation I ℱ :=
    { diag := Functor.const I ℱ
      ι :=
        { app := fun _ ↦ 𝟙 ℱ
          naturality := by
            intro X Y f
            simp }
      isColimit := by
        -- The constant one-object diagram has colimit `ℱ` itself.
        refine IsColimit.mk ?_ ?_ ?_
        · intro s
          exact s.ι.app ⟨ULift.up PUnit.unit⟩
        · intro s j
          cases j
          simp
        · intro s m hm
          simpa using hm ⟨ULift.up PUnit.unit⟩ }
  refine ⟨I, inferInstance, inferInstance, pres, ?_⟩
  intro i
  cases i
  simpa [pres]

/-- Helper for Lemma 18.30.7: transport a finite basis constructible-module cokernel
presentation across an isomorphism of module sheaves. -/
private theorem hasFiniteBasisConstructibleModuleCokernelPresentation_of_iso
    {X Y : SheafOfModules (ringSheaf J 𝒪)} (e : X ≅ Y)
    (hX : HasFiniteBasisConstructibleModuleCokernelPresentation 𝒪 B X) :
    HasFiniteBasisConstructibleModuleCokernelPresentation 𝒪 B Y := by
  -- Reuse the same finite cokernel data and transport only the identifying isomorphism.
  rcases hX with ⟨n, m, U, V, f, i, hU, hV⟩
  exact ⟨n, m, U, V, f, e.symm ≪≫ i, hU, hV⟩

/-- Helper for Lemma 18.30.7: a finite-index cokernel presentation over arbitrary finite index
types can be reindexed into the `Fin n` form used by the public predicate. -/
private theorem hasFiniteBasisConstructibleModuleCokernelPresentation_of_finiteTypes
    {X : SheafOfModules (ringSheaf J 𝒪)}
    {A K : Type u} [Fintype A] [Fintype K]
    (U : A → C) (V : K → C)
    (f :
      (∐ fun j : K ↦ localizedStructureModuleExtensionByZero 𝒪 (V j)) ⟶
        (∐ fun i : A ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)))
    (e : X ≅ cokernel f)
    (hU : ∀ i, U i ∈ B) (hV : ∀ j, V j ∈ B) :
    HasFiniteBasisConstructibleModuleCokernelPresentation 𝒪 B X := by
  let _ : HasColimitsOfShape (Discrete A) (SheafOfModules (ringSheaf J 𝒪)) :=
    Limits.hasColimitsOfShape_discrete (C := SheafOfModules (ringSheaf J 𝒪)) A
  let _ : HasColimitsOfShape (Discrete K) (SheafOfModules (ringSheaf J 𝒪)) :=
    Limits.hasColimitsOfShape_discrete (C := SheafOfModules (ringSheaf J 𝒪)) K
  let _ :
      HasColimitsOfShape (Discrete (Fin (Fintype.card A)))
        (SheafOfModules (ringSheaf J 𝒪)) :=
    Limits.hasColimitsOfShape_discrete
      (C := SheafOfModules (ringSheaf J 𝒪)) (Fin (Fintype.card A))
  let _ :
      HasColimitsOfShape (Discrete (Fin (Fintype.card K)))
        (SheafOfModules (ringSheaf J 𝒪)) :=
    Limits.hasColimitsOfShape_discrete
      (C := SheafOfModules (ringSheaf J 𝒪)) (Fin (Fintype.card K))
  let eA : Fin (Fintype.card A) ≃ A := (Fintype.equivFin A).symm
  let eK : Fin (Fintype.card K) ≃ K := (Fintype.equivFin K).symm
  let sourceIso :
      (∐ fun j : Fin (Fintype.card K) ↦ localizedStructureModuleExtensionByZero 𝒪 (V (eK j))) ≅
        (∐ fun j : K ↦ localizedStructureModuleExtensionByZero 𝒪 (V j)) :=
    Limits.Sigma.reindex eK (fun j : K ↦ localizedStructureModuleExtensionByZero 𝒪 (V j))
  let targetIso :
      (∐ fun i : Fin (Fintype.card A) ↦ localizedStructureModuleExtensionByZero 𝒪 (U (eA i))) ≅
        (∐ fun i : A ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)) :=
    Limits.Sigma.reindex eA (fun i : A ↦ localizedStructureModuleExtensionByZero 𝒪 (U i))
  let f' :
      (∐ fun j : Fin (Fintype.card K) ↦ localizedStructureModuleExtensionByZero 𝒪 (V (eK j))) ⟶
        (∐ fun i : Fin (Fintype.card A) ↦ localizedStructureModuleExtensionByZero 𝒪 (U (eA i))) :=
    sourceIso.hom ≫ f ≫ targetIso.inv
  let ecoker : cokernel f ≅ cokernel f' :=
    cokernel.mapIso f f' sourceIso.symm targetIso.symm (by simp [f'])
  -- Reindex both finite direct sums to `Fin` and transport the identified cokernel across the
  -- resulting conjugation isomorphism.
  refine
    ⟨Fintype.card A, Fintype.card K,
      fun i ↦ U (eA i), fun j ↦ V (eK j), f', e ≪≫ ecoker, ?_, ?_⟩
  · intro i
    exact hU (eA i)
  · intro j
    exact hV (eK j)

/-- Helper for Lemma 18.30.7: an epimorphism together with an epimorphic cover of its kernel
packages the target as the cokernel of the composite map. -/
lemma cokernelIso_of_epi_kernelCover
    {A B X : SheafOfModules (ringSheaf J 𝒪)} (φ : A ⟶ X) (ψ : B ⟶ kernel φ)
    [Epi φ] [Epi ψ] :
    X ≅ cokernel (ψ ≫ kernel.ι φ) := by
  let S : ShortComplex (SheafOfModules (ringSheaf J 𝒪)) :=
    ShortComplex.mk (ψ ≫ kernel.ι φ) φ (by simp [Category.assoc, kernel.condition])
  let T : ShortComplex (SheafOfModules (ringSheaf J 𝒪)) :=
    ShortComplex.mk (kernel.ι φ) φ (by simp)
  have hTExact : T.Exact := by
    -- The canonical kernel row is exact by the kernel universal property.
    simpa [T] using
      (ShortComplex.exact_of_f_is_kernel T (kernelIsKernel φ))
  let η : S ⟶ T :=
    { τ₁ := ψ
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [S, T, Category.assoc]
      comm₂₃ := by simp [S, T] }
  have hSExact : S.Exact := by
    -- Exactness descends across the epimorphic left comparison `ψ`.
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono η).2 hTExact
  obtain ⟨hcolim⟩ := (S.exact_and_epi_g_iff_g_is_cokernel).1 ⟨hSExact, inferInstance⟩
  -- The explicit cokernel of `ψ ≫ kernel.ι φ` is therefore canonically isomorphic to `X`.
  exact IsColimit.coconePointUniqueUpToIso
    (cokernelIsCokernel (ψ ≫ kernel.ι φ)) hcolim

/-- Helper for Lemma 18.30.7: `localizedStructureModuleExtensionByZero_homEquiv` is natural in
the target module sheaf. -/
private theorem localizedStructureModuleExtensionByZero_homEquiv_naturality_right
    {W : C} {ℱ 𝒢 : SheafOfModules (ringSheaf J 𝒪)}
    (β : localizedStructureModuleExtensionByZero 𝒪 W ⟶ ℱ) (α : ℱ ⟶ 𝒢) :
    localizedStructureModuleExtensionByZero_homEquiv J 𝒪 W 𝒢 (β ≫ α) =
      ((SheafOfModules.evaluation (ringSheaf J 𝒪) (op W)).map α)
        (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 W ℱ β) := by
  -- The owner equivalence is defined by target-functorial constructions, so this naturality is
  -- definitional.
  rfl

/-- Helper for Lemma 18.30.7: a morphism from one basis generator `j_{W!}\mathcal O_W` into a
coproduct of such generators factors through a single summand. -/
lemma basisConstructibleModuleMapFactorsThroughSingleSummand
    {W : C} (hW : W ∈ B) {A : Type u} (U : A → C)
    [HasColimitsOfShape (Discrete A) (SheafOfModules (ringSheaf J 𝒪))]
    (g : localizedStructureModuleExtensionByZero 𝒪 W ⟶
      (∐ fun a : A ↦ localizedStructureModuleExtensionByZero 𝒪 (U a))) :
    ∃ a : A, ∃ g_a : localizedStructureModuleExtensionByZero 𝒪 W ⟶
      localizedStructureModuleExtensionByZero 𝒪 (U a),
        g_a ≫ Limits.Sigma.ι
          (fun b : A ↦ localizedStructureModuleExtensionByZero 𝒪 (U b)) a = g := by
  let Gmod := SheafOfModules.evaluation (ringSheaf J 𝒪) (op W)
  let G :=
    Gmod ⋙ forget₂ (ModuleCat ((ringSheaf J 𝒪).1.obj (op W))) Type
  have hq : J.QuasiCompactObject W :=
    HasQuasiCompactBasisWithQuasiCompactFiberProducts.quasiCompactObject
      (J := J) (B := B) hW
  have hpresMod : PreservesColimitsOfShape (Discrete A) Gmod :=
    quasiCompactObject_module_evaluation_preserves_direct_sums
      (J := J) (𝒪 := ringSheaf J 𝒪) W hq A
  have hpres : PreservesColimitsOfShape (Discrete A) G := by
    let _ : PreservesColimitsOfShape (Discrete A) Gmod := hpresMod
    let _ :
        PreservesColimitsOfShape (Discrete A)
          (forget₂ (ModuleCat ((ringSheaf J 𝒪).1.obj (op W))) Type) := by
      infer_instance
    exact CategoryTheory.Limits.comp_preservesColimitsOfShape Gmod
      (forget₂ (ModuleCat ((ringSheaf J 𝒪).1.obj (op W))) Type)
  let F : Discrete A ⥤ SheafOfModules (ringSheaf J 𝒪) :=
    Discrete.functor (fun a : A ↦ localizedStructureModuleExtensionByZero 𝒪 (U a))
  let x : G.obj (∐ fun a : A ↦ localizedStructureModuleExtensionByZero 𝒪 (U a)) :=
    localizedStructureModuleExtensionByZero_homEquiv J 𝒪 W _ g
  let t : Cocone (F ⋙ G) := G.mapCocone (colimit.cocone F)
  have ht : IsColimit t := isColimitOfPreserves G (colimit.isColimit F)
  -- The preserved direct sum of sections is still a concrete coproduct, so the chosen section
  -- comes from one tagged summand.
  obtain ⟨a, ya, hya⟩ := CategoryTheory.Types.jointly_surjective_of_isColimit ht x
  let g_a : localizedStructureModuleExtensionByZero 𝒪 W ⟶
      localizedStructureModuleExtensionByZero 𝒪 (U a.as) :=
    (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 W
      (localizedStructureModuleExtensionByZero 𝒪 (U a.as))).symm ya
  refine ⟨a.as, g_a, ?_⟩
  apply (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 W _).injective
  -- After applying sections over `W`, the factorization statement becomes the representative
  -- identity supplied by the preserved coproduct colimit.
  rw [localizedStructureModuleExtensionByZero_homEquiv_naturality_right
    (J := J) (𝒪 := 𝒪) (β := g_a)
    (α := Limits.Sigma.ι
      (fun b : A ↦ localizedStructureModuleExtensionByZero 𝒪 (U b)) a.as)]
  have hsection :
      G.map
          (Limits.Sigma.ι
            (fun b : A ↦ localizedStructureModuleExtensionByZero 𝒪 (U b)) a.as) ya =
        x := by
    simpa [t, F] using hya
  simpa [g_a, x, G, Gmod] using hsection

/-- Helper for Lemma 18.30.7: a morphism from a finite coproduct of basis generators
`j_{V!}\mathcal O_V` into an arbitrary coproduct factors through a finite target coproduct. -/
lemma finiteSourceBasisConstructibleModuleMapFactorsThroughFiniteCoproduct
    {m : ℕ} {V : Fin m → C} (hV : ∀ j, V j ∈ B) {A : Type u} (U : A → C)
    [HasColimitsOfShape (Discrete A) (SheafOfModules (ringSheaf J 𝒪))]
    (g : (∐ fun j : Fin m ↦ localizedStructureModuleExtensionByZero 𝒪 (V j)) ⟶
      (∐ fun a : A ↦ localizedStructureModuleExtensionByZero 𝒪 (U a))) :
    ∃ a : Fin m → A,
      ∃ g' :
        (∐ fun j : Fin m ↦ localizedStructureModuleExtensionByZero 𝒪 (V j)) ⟶
          (∐ fun j : Fin m ↦ localizedStructureModuleExtensionByZero 𝒪 (U (a j))),
        g' ≫ Limits.Sigma.desc (fun j : Fin m ↦
          Limits.Sigma.ι
            (fun b : A ↦ localizedStructureModuleExtensionByZero 𝒪 (U b)) (a j)) = g := by
  -- Factor each finite source summand through one target summand using compactness of the basis
  -- generators supplied by Lemma `18.30.4`.
  choose a g₁ hg₁ using fun j : Fin m ↦
    basisConstructibleModuleMapFactorsThroughSingleSummand
      (J := J) (𝒪 := 𝒪) (B := B) (W := V j) (hW := hV j) (U := U)
      (g := Limits.Sigma.ι
        (fun k : Fin m ↦ localizedStructureModuleExtensionByZero 𝒪 (V k)) j ≫ g)
  let g' :
      (∐ fun j : Fin m ↦ localizedStructureModuleExtensionByZero 𝒪 (V j)) ⟶
        (∐ fun j : Fin m ↦ localizedStructureModuleExtensionByZero 𝒪 (U (a j))) :=
    Limits.Sigma.desc (fun j : Fin m ↦
      g₁ j ≫ Limits.Sigma.ι
        (fun k : Fin m ↦ localizedStructureModuleExtensionByZero 𝒪 (U (a k))) j)
  refine ⟨a, g', ?_⟩
  -- Compare the two maps after restricting to each source summand.
  apply Limits.Sigma.hom_ext
  intro j
  simp only [g', Category.assoc, Limits.Sigma.ι_desc]
  simpa using hg₁ j

local instance (ι : Type u) :
    HasColimitsOfShape (Finset (Discrete ι)) (SheafOfModules (ringSheaf J 𝒪)) := by
  -- Module sheaves also have all small colimits, so the finite-support index categories are
  -- available automatically.
  infer_instance

/-- Helper for Lemma 18.30.7: the full coproduct of a family of module sheaves is the colimit of
its finite-subcoproduct diagram indexed by `Finset (Discrete ι)`. -/
noncomputable def finiteSubcoproductsModuleCoconeIsColimit
    {ι : Type u} (F : ι → SheafOfModules (ringSheaf J 𝒪)) :
    IsColimit (finiteSubcoproductsCocone F) := by
  -- This is again the generic finite-subcoproduct colimit construction, now in module sheaves.
  exact isColimitFiniteSubproductsCocone F

/-- Helper for Lemma 18.30.7: the colimit of the finite-subcoproduct module diagram is canonically
the ambient coproduct. -/
noncomputable def finiteSubcoproductsModuleColimitIso
    {ι : Type u} (F : ι → SheafOfModules (ringSheaf J 𝒪)) :
    ∐ F ≅ colimit (liftToFinsetObj (Discrete.functor F)) := by
  -- Compare the standard finite-subcoproduct cocone with the ambient coproduct cocone.
  exact (finiteSubcoproductsModuleCoconeIsColimit (J := J) (𝒪 := 𝒪) F).coconePointUniqueUpToIso
    (colimit.isColimit (liftToFinsetObj (Discrete.functor F)))

/-- Helper for Lemma 18.30.7: the `hom` of the finite-subcoproduct colimit isomorphism sends the
explicit finite-stage coproduct inclusion to the corresponding colimit leg. -/
lemma finiteSubcoproductsModuleColimitIso_hom_app
    {ι : Type u} (F : ι → SheafOfModules (ringSheaf J 𝒪)) (s : Finset (Discrete ι)) :
    Limits.Sigma.desc (fun i : s ↦ Limits.Sigma.ι F i.1.as) ≫
        (finiteSubcoproductsModuleColimitIso (J := J) (𝒪 := 𝒪) F).hom =
      colimit.ι (liftToFinsetObj (Discrete.functor F)) s := by
  -- Proof comment: as on the sheaf side, the colimit comparison is computed on cocone legs.
  rw [show Limits.Sigma.desc (fun i : s ↦ Limits.Sigma.ι F i.1.as) =
      (finiteSubcoproductsCocone F).ι.app s by
      rw [finiteSubcoproductsCocone_ι_app]]
  simpa [finiteSubcoproductsModuleColimitIso] using
    (IsColimit.comp_coconePointUniqueUpToIso_hom
      (finiteSubcoproductsModuleCoconeIsColimit (J := J) (𝒪 := 𝒪) F)
      (colimit.isColimit (liftToFinsetObj (Discrete.functor F)))
      s)

/-- Helper for Lemma 18.30.7: one source generator of the infinite module map already factors
through a finite target subcoproduct. -/
lemma basisConstructibleModuleMapFactorsThroughFiniteSubcoproduct
    {A K : Type u} (U : A → C) (V : K → C)
    (hV : ∀ j, V j ∈ B)
    (f :
      (∐ fun j : K ↦ localizedStructureModuleExtensionByZero 𝒪 (V j)) ⟶
        (∐ fun i : A ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)))
    (j : K) :
    ∃ t : Finset (Discrete A),
      ∃ f₀ :
        localizedStructureModuleExtensionByZero 𝒪 (V j) ⟶
          (liftToFinsetObj
            (Discrete.functor
              (fun i : A ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)))).obj t,
        f₀ ≫
            ((finiteSubcoproductsCocone
              (fun i : A ↦ localizedStructureModuleExtensionByZero 𝒪 (U i))).ι.app t) =
          Limits.Sigma.ι
              (fun b : K ↦ localizedStructureModuleExtensionByZero 𝒪 (V b)) j ≫
            f := by
  classical
  let F : A → SheafOfModules (ringSheaf J 𝒪) :=
    fun i ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)
  let D : Finset (Discrete A) ⥤ SheafOfModules (ringSheaf J 𝒪) :=
    liftToFinsetObj (Discrete.functor F)
  -- Factor the chosen source summand through one target generator and regard that target as a
  -- one-point finite support.
  obtain ⟨i, f₁, hf₁⟩ :=
    basisConstructibleModuleMapFactorsThroughSingleSummand
      (J := J) (𝒪 := 𝒪) (B := B) (W := V j) (hW := hV j) (U := U)
      (g := Limits.Sigma.ι
        (fun b : K ↦ localizedStructureModuleExtensionByZero 𝒪 (V b)) j ≫ f)
  let t : Finset (Discrete A) := {⟨i⟩}
  let idx : t := ⟨⟨i⟩, by simp [t]⟩
  let f₀ :
      localizedStructureModuleExtensionByZero 𝒪 (V j) ⟶ D.obj t :=
    f₁ ≫ Limits.Sigma.ι (fun a : t ↦ localizedStructureModuleExtensionByZero 𝒪 (U a.1.as)) idx
  refine ⟨t, f₀, ?_⟩
  -- Expanding the finite-subcoproduct inclusion at the unique chosen target recovers the original
  -- source summand map.
  calc
    f₀ ≫ ((finiteSubcoproductsCocone F).ι.app t) =
        f₁ ≫ Limits.Sigma.ι F i := by
          simp [f₀, D, F, t, idx, Category.assoc, finiteSubcoproductsCocone_ι_app]
    _ =
        Limits.Sigma.ι
            (fun b : K ↦ localizedStructureModuleExtensionByZero 𝒪 (V b)) j ≫
          f := hf₁

/-- Helper for Lemma 18.30.7: a chosen finite factorization of one source generator of the
infinite module map can be enlarged along any bigger finite target support. -/
lemma basisConstructibleModuleMapFactorsThroughTargetStage
    {A K : Type u} (U : A → C) (V : K → C)
    (hV : ∀ j, V j ∈ B)
    (f :
      (∐ fun j : K ↦ localizedStructureModuleExtensionByZero 𝒪 (V j)) ⟶
        (∐ fun i : A ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)))
    (j : K) (t : Finset (Discrete A))
    (ht : (Classical.choose
      (basisConstructibleModuleMapFactorsThroughFiniteSubcoproduct
        (J := J) (𝒪 := 𝒪) (B := B) U V hV f j)) ≤ t) :
    ∃ fₜ :
        localizedStructureModuleExtensionByZero 𝒪 (V j) ⟶
          (liftToFinsetObj
            (Discrete.functor
              (fun i : A ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)))).obj t,
      fₜ ≫
          ((finiteSubcoproductsCocone
            (fun i : A ↦ localizedStructureModuleExtensionByZero 𝒪 (U i))).ι.app t) =
        Limits.Sigma.ι
            (fun b : K ↦ localizedStructureModuleExtensionByZero 𝒪 (V b)) j ≫
          f := by
  classical
  let F : A → SheafOfModules (ringSheaf J 𝒪) :=
    fun i ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)
  let D : Finset (Discrete A) ⥤ SheafOfModules (ringSheaf J 𝒪) :=
    liftToFinsetObj (Discrete.functor F)
  let s : Finset (Discrete A) := Classical.choose
    (basisConstructibleModuleMapFactorsThroughFiniteSubcoproduct
      (J := J) (𝒪 := 𝒪) (B := B) U V hV f j)
  let f₀ :
      localizedStructureModuleExtensionByZero 𝒪 (V j) ⟶ D.obj s :=
    Classical.choose <|
      Classical.choose <|
        basisConstructibleModuleMapFactorsThroughFiniteSubcoproduct
          (J := J) (𝒪 := 𝒪) (B := B) U V hV f j
  have hf₀ :
      f₀ ≫ ((finiteSubcoproductsCocone F).ι.app s) =
        Limits.Sigma.ι
            (fun b : K ↦ localizedStructureModuleExtensionByZero 𝒪 (V b)) j ≫
          f := by
    -- Unpack the chosen finite factorization and record its comparison with the ambient map.
    exact Classical.choose <|
      Classical.choose <|
        basisConstructibleModuleMapFactorsThroughFiniteSubcoproduct
          (J := J) (𝒪 := 𝒪) (B := B) U V hV f j
  refine ⟨f₀ ≫ D.map (homOfLE ht), ?_⟩
  -- Postcompose the chosen factorization with the canonical enlargement map into the bigger
  -- finite target support.
  calc
    (f₀ ≫ D.map (homOfLE ht)) ≫ ((finiteSubcoproductsCocone F).ι.app t) =
        f₀ ≫ ((finiteSubcoproductsCocone F).ι.app s) := by
          rw [Category.assoc, (finiteSubcoproductsCocone F).w (homOfLE ht)]
    _ =
        Limits.Sigma.ι
            (fun b : K ↦ localizedStructureModuleExtensionByZero 𝒪 (V b)) j ≫
          f := hf₀

/-- Helper for Lemma 18.30.7: a support-closed finite stage already has a finite basis cokernel
presentation once its finite arrow is fixed. -/
private theorem hasFiniteBasisConstructibleModuleCokernelPresentation_of_supportPairStage
    {X : SheafOfModules (ringSheaf J 𝒪)} {A K : Type u}
    (U : A → C) (V : K → C)
    (hU : ∀ i, U i ∈ B) (hV : ∀ j, V j ∈ B)
    {supp : Finset (Discrete K) → Finset (Discrete A)}
    (p : CategoryTheory.GrothendieckTopology.supportPairIndex supp)
    (f :
      (∐ fun j : p.1.1 ↦ localizedStructureModuleExtensionByZero 𝒪 (V j.1.as)) ⟶
        (∐ fun i : p.1.2 ↦ localizedStructureModuleExtensionByZero 𝒪 (U i.1.as)))
    (e : X ≅ cokernel f) :
    HasFiniteBasisConstructibleModuleCokernelPresentation 𝒪 B X := by
  classical
  -- Reindex the stage along the finite subtype carriers supplied by the two supports.
  exact hasFiniteBasisConstructibleModuleCokernelPresentation_of_finiteTypes
    (𝒪 := 𝒪) (B := B)
    (U := fun i : p.1.2 ↦ U i.1.as) (V := fun j : p.1.1 ↦ V j.1.as)
    f e
    (fun i ↦ hU i.1.as)
    (fun j ↦ hV j.1.as)

-- Proof sketch: start from the epimorphism of Lemma `18.30.6 (2)` available in Situation
-- `18.30.5` from a possibly infinite direct sum of modules `j_{U!}\mathcal O_U` with `U ∈ B`.
-- Apply Lemma `18.30.4` to the quasi-compact basis objects to show that morphisms out of the
-- finite source pieces factor through finite subcoproducts, so the resulting cokernels over
-- finite subdiagrams form a filtered colimit presentation of `ℱ`.
/-- Lemma 18.30.7 (2): in Situation `18.30.5`, every `\mathcal O`-module is a filtered colimit
of modules admitting finite cokernel presentations by sums of the extensions by zero
`j_{U!}\mathcal O_U` with `U ∈ B`. -/
theorem exists_filteredColimitPresentation_by_finite_basis_constructibleModule_cokernels
    (ℱ : SheafOfModules (ringSheaf J 𝒪)) :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I)
      (pres : ColimitPresentation I ℱ),
        ∀ i, HasFiniteBasisConstructibleModuleCokernelPresentation 𝒪 B (pres.diag.obj i) :=
by
  -- Route correction: first package the two-step infinite presentation into one explicit cokernel.
  classical
  obtain ⟨A, K, U, V, φ, ψ, hφ, hψ, hU, hV⟩ :=
    existsBasisConstructibleModuleKernelPresentation (𝒪 := 𝒪) (B := B) ℱ
  let _ : Epi φ := hφ
  let _ : Epi ψ := hψ
  let g : (∐ fun j : K ↦ localizedStructureModuleExtensionByZero 𝒪 (V j)) ⟶ kernel φ :=
    ψ
  let e : ℱ ≅ cokernel (g ≫ kernel.ι φ) :=
    cokernelIso_of_epi_kernelCover (𝒪 := 𝒪) (φ := φ) (ψ := g)
  choose componentSupport f₀ hf₀ using
    fun j : K ↦
      basisConstructibleModuleMapFactorsThroughFiniteSubcoproduct
        (J := J) (𝒪 := 𝒪) (B := B) U V hV (g ≫ kernel.ι φ) j
  let supp : Finset (Discrete K) → Finset (Discrete A) :=
    fun s ↦ s.biUnion (fun j ↦ componentSupport j.as)
  have hsupp_union :
      ∀ s₁ s₂ : Finset (Discrete K), supp (s₁ ∪ s₂) ≤ supp s₁ ∪ supp s₂ := by
    intro s₁ s₂
    simpa [supp] using
      CategoryTheory.GrothendieckTopology.supportOfComponents_union_le componentSupport s₁ s₂
  have hsupp_mono : Monotone supp := by
    simpa [supp] using
      CategoryTheory.GrothendieckTopology.supportOfComponents_mono componentSupport
  have hsupp_empty : supp ∅ = ∅ := by
    simpa [supp] using
      CategoryTheory.GrothendieckTopology.supportOfComponents_empty componentSupport
  let I : Type u := CategoryTheory.GrothendieckTopology.supportPairIndex supp
  let _ : IsFiltered I :=
    CategoryTheory.GrothendieckTopology.isFiltered_supportPairStages supp hsupp_union
  let f :
      (∐ fun j : K ↦ localizedStructureModuleExtensionByZero 𝒪 (V j)) ⟶
        (∐ fun i : A ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)) :=
    g ≫ kernel.ι φ
  let sourceF : K → SheafOfModules (ringSheaf J 𝒪) :=
    fun j ↦ localizedStructureModuleExtensionByZero 𝒪 (V j)
  let targetF : A → SheafOfModules (ringSheaf J 𝒪) :=
    fun i ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)
  let sourceDiag : Finset (Discrete K) ⥤ SheafOfModules (ringSheaf J 𝒪) :=
    liftToFinsetObj (Discrete.functor sourceF)
  let targetDiag : Finset (Discrete A) ⥤ SheafOfModules (ringSheaf J 𝒪) :=
    liftToFinsetObj (Discrete.functor targetF)
  have hcomponent_le_target :
      ∀ (p : I) (j : p.1.1), componentSupport j.1.as ≤ p.1.2 := by
    intro p j
    exact le_trans
      (CategoryTheory.GrothendieckTopology.componentSupport_le_supportOf_mem
        componentSupport j.2)
      p.2
  let stageMap : (p : I) →
      (∐ fun j : p.1.1 ↦ localizedStructureModuleExtensionByZero 𝒪 (V j.1.as)) ⟶
        (∐ fun i : p.1.2 ↦ localizedStructureModuleExtensionByZero 𝒪 (U i.1.as)) :=
    fun p ↦
      Limits.Sigma.desc fun j : p.1.1 ↦
        Classical.choose <|
          basisConstructibleModuleMapFactorsThroughTargetStage
            (J := J) (𝒪 := 𝒪) (B := B) U V hV f j.1.as p.1.2
            (hcomponent_le_target p j)
  have stageMap_fac :
      ∀ (p : I) (j : p.1.1),
        Limits.Sigma.ι
            (fun b : p.1.1 ↦ localizedStructureModuleExtensionByZero 𝒪 (V b.1.as)) j ≫
            stageMap p ≫ ((finiteSubcoproductsCocone targetF).ι.app p.1.2) =
          Limits.Sigma.ι sourceF j.1.as ≫ f := by
    intro p j
    dsimp [stageMap]
    simp [basisConstructibleModuleMapFactorsThroughTargetStage, sourceF, targetF, targetDiag,
      Category.assoc]
  have stageMap_naturality :
      ∀ {p q : I} (u : p ⟶ q),
        stageMap p ≫
            targetDiag.map (homOfLE (show p.1.2 ≤ q.1.2 from (leOfHom u).2)) =
          sourceDiag.map (homOfLE (show p.1.1 ≤ q.1.1 from (leOfHom u).1)) ≫
            stageMap q := by
    intro p q u
    apply Limits.Sigma.hom_ext
    intro j
    dsimp [stageMap, sourceDiag, targetDiag]
    simp [basisConstructibleModuleMapFactorsThroughTargetStage, Category.assoc]
  let D : I ⥤ WalkingParallelPair ⥤ SheafOfModules (ringSheaf J 𝒪) := by
    refine
      { obj := fun p ↦ parallelPair (stageMap p) 0
        map := fun {p q} u ↦
          { app := fun z ↦ match z with
              | WalkingParallelPair.zero =>
                  sourceDiag.map (homOfLE (show p.1.1 ≤ q.1.1 from (leOfHom u).1))
              | WalkingParallelPair.one =>
                  targetDiag.map (homOfLE (show p.1.2 ≤ q.1.2 from (leOfHom u).2))
            naturality := by
              intro z z' g
              cases g
              · simp
              · simpa using stageMap_naturality u
              · simp }
        map_id := by
          intro p
          ext z
          cases z <;> simp [sourceDiag, targetDiag]
        map_comp := by
          intro p q r u v
          ext z
          cases z <;> simp [sourceDiag, targetDiag] }
  let c : Cocone D := by
    refine
      { pt := parallelPair f 0
        ι :=
          { app := fun p ↦
              { app := fun z ↦ match z with
                  | WalkingParallelPair.zero =>
                      ((finiteSubcoproductsCocone sourceF).ι.app p.1.1)
                  | WalkingParallelPair.one =>
                      ((finiteSubcoproductsCocone targetF).ι.app p.1.2)
                naturality := by
                  intro z z' g
                  cases g
                  · simp
                  · apply Limits.Sigma.hom_ext
                    intro j
                    simpa [sourceF, targetF, Category.assoc] using stageMap_fac p j
                  · simp }
            naturality := by
              intro p q u
              ext z
              cases z <;> simp [sourceDiag, targetDiag] } }
  let _ :
      Functor.Final
        (CategoryTheory.GrothendieckTopology.supportPairSourceProjection supp) :=
    CategoryTheory.GrothendieckTopology.supportPairSourceProjection_final supp hsupp_mono
  let _ :
      Functor.Final
        (CategoryTheory.GrothendieckTopology.supportPairTargetProjection supp) :=
    CategoryTheory.GrothendieckTopology.supportPairTargetProjection_final supp hsupp_empty
  have hzero :
      IsColimit (((evaluation _ _).obj WalkingParallelPair.zero).mapCocone c) := by
    exact
      (Functor.Final.isColimitWhiskerEquiv
        (CategoryTheory.GrothendieckTopology.supportPairSourceProjection supp)
        (finiteSubcoproductsCocone sourceF)).symm
        (finiteSubcoproductsModuleCoconeIsColimit (J := J) (𝒪 := 𝒪) sourceF)
  have hone :
      IsColimit (((evaluation _ _).obj WalkingParallelPair.one).mapCocone c) := by
    exact
      (Functor.Final.isColimitWhiskerEquiv
        (CategoryTheory.GrothendieckTopology.supportPairTargetProjection supp)
        (finiteSubcoproductsCocone targetF)).symm
        (finiteSubcoproductsModuleCoconeIsColimit (J := J) (𝒪 := 𝒪) targetF)
  have hc : IsColimit c := by
    -- Proof comment: as on the sheaf side, colimits of `WalkingParallelPair`-diagrams are
    -- reflected by evaluation at the two endpoints.
    refine evaluationJointlyReflectsColimits c ?_
    intro z
    cases z
    · simpa [D, c, sourceDiag,
        CategoryTheory.GrothendieckTopology.supportPairSourceProjection] using hzero
    · simpa [D, c, targetDiag,
        CategoryTheory.GrothendieckTopology.supportPairTargetProjection] using hone
  let pres : ColimitPresentation I ℱ :=
    { diag := D ⋙ colim
      ι :=
        { app := fun p ↦ (colim.mapCocone c).ι.app p ≫ e.inv
          naturality := by
            intro p q u
            simpa [Category.assoc] using
              congrArg (fun k ↦ k ≫ e.inv) ((colim.mapCocone c).ι.naturality u) }
      isColimit := by
        have hcolim : IsColimit (colim.mapCocone c) :=
          isColimitOfPreserves colim hc
        refine IsColimit.ofIsoColimit hcolim ?_
        refine Cocone.ext e ?_
        intro p
        simp }
  refine ⟨I, inferInstance, inferInstance, pres, ?_⟩
  intro p
  -- Proof comment: every stage cokernel is built from finite source and target supports by
  -- construction, so the Chapter 18 public predicate applies immediately.
  simpa [pres, D, f] using
    hasFiniteBasisConstructibleModuleCokernelPresentation_of_supportPairStage
      (𝒪 := 𝒪) (B := B) U V hU hV p (stageMap p) (Iso.refl _)

end SheafOfModules.RingedSite
