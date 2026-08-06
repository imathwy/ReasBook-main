import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap16.Definition_16_1_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap16.Definition_16_1_3

open CategoryTheory Simplicial

universe u

-- The source-facing operators on singular simplices are the degreewise face and degeneracy maps of
-- the canonical singular simplicial set `TopCat.toSSet.obj X`, transported along
-- `singularSimplexEquiv`.

/-- Construction 16.1.4 (1): the `i`-th face operator on singular simplices is defined by
precomposition with the `i`-th face map `Δ^n → Δ^(n + 1)`. -/
noncomputable abbrev singularFaceOperator (n : ℕ) (i : Fin (n + 2))
    (X : Type u) [TopologicalSpace X] :
    singularSimplex (n + 1) X → singularSimplex n X :=
  fun σ ↦
    σ.comp ⟨standardSimplexFaceMap n i, continuous_standardSimplexFaceMap n i⟩

/-- Construction 16.1.4 (2): the `i`-th degeneracy operator on singular simplices is defined by
precomposition with the `i`-th degeneracy map `Δ^(n + 1) → Δ^n`. -/
noncomputable abbrev singularDegeneracyOperator (n : ℕ) (i : Fin (n + 1))
    (X : Type u) [TopologicalSpace X] :
    singularSimplex n X → singularSimplex (n + 1) X :=
  fun σ ↦
    σ.comp ⟨standardSimplexDegeneracyMap n i, continuous_standardSimplexDegeneracyMap n i⟩

/-- Under `singularSimplexEquiv`, the source-facing face operator is the canonical face map on the
singular simplicial set `TopCat.toSSet.obj X`. -/
@[simp] theorem singularSimplexEquiv_symm_faceOperator
    (n : ℕ) (i : Fin (n + 2)) (X : Type u) [TopologicalSpace X]
    (σ : singularSimplex (n + 1) X) :
    (singularSimplexEquiv n (TopCat.of X)).symm (singularFaceOperator n i X σ) =
      (TopCat.toSSet.obj (TopCat.of X)).δ i
        ((singularSimplexEquiv (n + 1) (TopCat.of X)).symm σ) :=
  rfl

/-- Under `singularSimplexEquiv`, the source-facing degeneracy operator is the canonical
degeneracy map on the singular simplicial set `TopCat.toSSet.obj X`. -/
@[simp] theorem singularSimplexEquiv_symm_degeneracyOperator
    (n : ℕ) (i : Fin (n + 1)) (X : Type u) [TopologicalSpace X] (σ : singularSimplex n X) :
    (singularSimplexEquiv (n + 1) (TopCat.of X)).symm (singularDegeneracyOperator n i X σ) =
      (TopCat.toSSet.obj (TopCat.of X)).σ i
        ((singularSimplexEquiv n (TopCat.of X)).symm σ) :=
  rfl

/-- Construction 16.1.4 (3): the face operators satisfy the first simplicial identity. -/
theorem singularFaceOperator_comp_singularFaceOperator
    (n : ℕ) {i j : Fin (n + 2)} (hij : i ≤ j) (X : Type u) [TopologicalSpace X] :
    singularFaceOperator n i X ∘ singularFaceOperator (n + 1) j.succ X =
      singularFaceOperator n j X ∘ singularFaceOperator (n + 1) (Fin.castSucc i) X := by
  funext σ
  have h :
      (singularSimplexEquiv n (TopCat.of X)).symm
          ((singularFaceOperator n i X ∘ singularFaceOperator (n + 1) j.succ X) σ) =
        (singularSimplexEquiv n (TopCat.of X)).symm
          ((singularFaceOperator n j X ∘ singularFaceOperator (n + 1) (Fin.castSucc i) X) σ) := by
    change
      (TopCat.toSSet.obj (TopCat.of X)).δ i
          ((TopCat.toSSet.obj (TopCat.of X)).δ j.succ
            ((singularSimplexEquiv (n + 2) (TopCat.of X)).symm σ)) =
        (TopCat.toSSet.obj (TopCat.of X)).δ j
          ((TopCat.toSSet.obj (TopCat.of X)).δ (Fin.castSucc i)
            ((singularSimplexEquiv (n + 2) (TopCat.of X)).symm σ))
    exact
      congrFun ((TopCat.toSSet.obj (TopCat.of X)).δ_comp_δ hij)
        ((singularSimplexEquiv (n + 2) (TopCat.of X)).symm σ)
  exact (singularSimplexEquiv n (TopCat.of X)).symm.injective h

/-- Construction 16.1.4 (4): the face and degeneracy operators satisfy the second simplicial
identity when `i ≤ j`. -/
theorem singularFaceOperator_comp_singularDegeneracyOperator_of_le
    (n : ℕ) {i : Fin (n + 2)} {j : Fin (n + 1)} (hij : i ≤ Fin.castSucc j)
    (X : Type u) [TopologicalSpace X] :
    singularDegeneracyOperator n j X ∘ singularFaceOperator n i X =
      singularFaceOperator (n + 1) (Fin.castSucc i) X ∘
        singularDegeneracyOperator (n + 1) j.succ X := by
  funext σ
  have h :
      (singularSimplexEquiv (n + 1) (TopCat.of X)).symm
          ((singularDegeneracyOperator n j X ∘ singularFaceOperator n i X) σ) =
        (singularSimplexEquiv (n + 1) (TopCat.of X)).symm
          ((singularFaceOperator (n + 1) (Fin.castSucc i) X ∘
              singularDegeneracyOperator (n + 1) j.succ X) σ) := by
    change
      (TopCat.toSSet.obj (TopCat.of X)).σ j
          ((TopCat.toSSet.obj (TopCat.of X)).δ i
            ((singularSimplexEquiv (n + 1) (TopCat.of X)).symm σ)) =
        (TopCat.toSSet.obj (TopCat.of X)).δ (Fin.castSucc i)
          ((TopCat.toSSet.obj (TopCat.of X)).σ j.succ
            ((singularSimplexEquiv (n + 1) (TopCat.of X)).symm σ))
    exact
      congrFun (((TopCat.toSSet.obj (TopCat.of X)).δ_comp_σ_of_le hij).symm)
        ((singularSimplexEquiv (n + 1) (TopCat.of X)).symm σ)
  exact (singularSimplexEquiv (n + 1) (TopCat.of X)).symm.injective h

/-- Construction 16.1.4 (5): the face and degeneracy operators satisfy the identity
`d_i s_i = 𝟙`. -/
theorem singularFaceOperator_comp_singularDegeneracyOperator_self
    (n : ℕ) {i : Fin (n + 1)} (X : Type u) [TopologicalSpace X] :
    singularFaceOperator n (Fin.castSucc i) X ∘ singularDegeneracyOperator n i X = id := by
  funext σ
  have h :
      (singularSimplexEquiv n (TopCat.of X)).symm
          ((singularFaceOperator n (Fin.castSucc i) X ∘ singularDegeneracyOperator n i X) σ) =
        (singularSimplexEquiv n (TopCat.of X)).symm
          ((id : singularSimplex n X → singularSimplex n X) σ) := by
    change
      (TopCat.toSSet.obj (TopCat.of X)).δ (Fin.castSucc i)
          ((TopCat.toSSet.obj (TopCat.of X)).σ i
            ((singularSimplexEquiv n (TopCat.of X)).symm σ)) =
        (singularSimplexEquiv n (TopCat.of X)).symm σ
    exact
      congrFun ((TopCat.toSSet.obj (TopCat.of X)).δ_comp_σ_self)
        ((singularSimplexEquiv n (TopCat.of X)).symm σ)
  exact (singularSimplexEquiv n (TopCat.of X)).symm.injective h

/-- Construction 16.1.4 (6): the face and degeneracy operators satisfy the identity
`d_(i + 1) s_i = 𝟙`. -/
theorem singularFaceOperator_comp_singularDegeneracyOperator_succ
    (n : ℕ) {i : Fin (n + 1)} (X : Type u) [TopologicalSpace X] :
    singularFaceOperator n i.succ X ∘ singularDegeneracyOperator n i X = id := by
  funext σ
  have h :
      (singularSimplexEquiv n (TopCat.of X)).symm
          ((singularFaceOperator n i.succ X ∘ singularDegeneracyOperator n i X) σ) =
        (singularSimplexEquiv n (TopCat.of X)).symm
          ((id : singularSimplex n X → singularSimplex n X) σ) := by
    change
      (TopCat.toSSet.obj (TopCat.of X)).δ i.succ
          ((TopCat.toSSet.obj (TopCat.of X)).σ i
            ((singularSimplexEquiv n (TopCat.of X)).symm σ)) =
        (singularSimplexEquiv n (TopCat.of X)).symm σ
    exact
      congrFun ((TopCat.toSSet.obj (TopCat.of X)).δ_comp_σ_succ)
        ((singularSimplexEquiv n (TopCat.of X)).symm σ)
  exact (singularSimplexEquiv n (TopCat.of X)).symm.injective h

/-- Construction 16.1.4 (7): the face and degeneracy operators satisfy the fourth simplicial
identity when `j < i`. -/
theorem singularFaceOperator_comp_singularDegeneracyOperator_of_gt
    (n : ℕ) {i : Fin (n + 2)} {j : Fin (n + 1)} (hij : Fin.castSucc j < i)
    (X : Type u) [TopologicalSpace X] :
    singularFaceOperator (n + 1) i.succ X ∘
        singularDegeneracyOperator (n + 1) (Fin.castSucc j) X =
      singularDegeneracyOperator n j X ∘ singularFaceOperator n i X := by
  funext σ
  have h :
      (singularSimplexEquiv (n + 1) (TopCat.of X)).symm
          ((singularFaceOperator (n + 1) i.succ X ∘
              singularDegeneracyOperator (n + 1) (Fin.castSucc j) X) σ) =
        (singularSimplexEquiv (n + 1) (TopCat.of X)).symm
          ((singularDegeneracyOperator n j X ∘ singularFaceOperator n i X) σ) := by
    change
      (TopCat.toSSet.obj (TopCat.of X)).δ i.succ
          ((TopCat.toSSet.obj (TopCat.of X)).σ (Fin.castSucc j)
            ((singularSimplexEquiv (n + 1) (TopCat.of X)).symm σ)) =
        (TopCat.toSSet.obj (TopCat.of X)).σ j
          ((TopCat.toSSet.obj (TopCat.of X)).δ i
            ((singularSimplexEquiv (n + 1) (TopCat.of X)).symm σ))
    exact
      congrFun ((TopCat.toSSet.obj (TopCat.of X)).δ_comp_σ_of_gt hij)
        ((singularSimplexEquiv (n + 1) (TopCat.of X)).symm σ)
  exact (singularSimplexEquiv (n + 1) (TopCat.of X)).symm.injective h

/-- Construction 16.1.4 (8): the degeneracy operators satisfy the fifth simplicial identity. -/
theorem singularDegeneracyOperator_comp_singularDegeneracyOperator
    (n : ℕ) {i j : Fin (n + 1)} (hij : i ≤ j) (X : Type u) [TopologicalSpace X] :
    singularDegeneracyOperator (n + 1) (Fin.castSucc i) X ∘ singularDegeneracyOperator n j X =
      singularDegeneracyOperator (n + 1) j.succ X ∘ singularDegeneracyOperator n i X := by
  funext σ
  have h :
      (singularSimplexEquiv (n + 2) (TopCat.of X)).symm
          ((singularDegeneracyOperator (n + 1) (Fin.castSucc i) X ∘
              singularDegeneracyOperator n j X) σ) =
        (singularSimplexEquiv (n + 2) (TopCat.of X)).symm
          ((singularDegeneracyOperator (n + 1) j.succ X ∘ singularDegeneracyOperator n i X) σ) := by
    change
      (TopCat.toSSet.obj (TopCat.of X)).σ (Fin.castSucc i)
          ((TopCat.toSSet.obj (TopCat.of X)).σ j
            ((singularSimplexEquiv n (TopCat.of X)).symm σ)) =
        (TopCat.toSSet.obj (TopCat.of X)).σ j.succ
          ((TopCat.toSSet.obj (TopCat.of X)).σ i
            ((singularSimplexEquiv n (TopCat.of X)).symm σ))
    exact
      congrFun ((TopCat.toSSet.obj (TopCat.of X)).σ_comp_σ hij)
        ((singularSimplexEquiv n (TopCat.of X)).symm σ)
  exact (singularSimplexEquiv (n + 2) (TopCat.of X)).symm.injective h
