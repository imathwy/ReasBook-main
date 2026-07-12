import StacksProject_2024.Chap10.Lemma_10_75_3_Support.Base

open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂ ComplexShape

noncomputable section

universe u

section

variable {R : Type u} [Ring R]

/-- Helper for Chap10 Lemma 10 75 3: the row comparison component has the expected value on
each total-complex summand. -/
@[reassoc]
private theorem ιTotal_totalToRowCokernelComponent
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    (i j n : ℕ) (h : ComplexShape.π (down ℕ) (down ℕ) (down ℕ) (i, j) = n) :
    A.ιTotal (down ℕ) i j n h ≫ totalToRowCokernelComponent A n =
      if hi : i = 0 then
        (HomologicalComplex₂.XXIsoOfEq (ModuleCat R) (down ℕ) (down ℕ) A hi
          (by simpa [hi] using h)).hom ≫ cokernel.π ((A.d 1 0).f n)
      else
        0 := by
  -- Re-open the owner computation rule locally so this support file can use it after the split
  -- into `Base` and `Core`.
  simp [totalToRowCokernelComponent]

/-- Helper for Chap10 Lemma 10 75 3: a `Fin (n + 1)` horizontal index and its complement
lie on the total-degree `n` antidiagonal. -/
private theorem totalAntidiagonalDegree (n : ℕ) (i : Fin (n + 1)) :
    ComplexShape.π (down ℕ) (down ℕ) (down ℕ) (i.1, n - i.1) = n := by
  -- The finite bound on `i` says precisely that `i + (n - i) = n`.
  simp [ComplexShape.π]
  omega

/-- Helper for Chap10 Lemma 10 75 3: a finite antidiagonal family of maps assembles into a
map to the total complex in degree `n`. -/
noncomputable def totalAntidiagonalLift
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    {T : ModuleCat R} (n : ℕ)
    (x : ∀ i : Fin (n + 1), T ⟶ (A.X i.1).X (n - i.1)) :
    T ⟶ (A.total (down ℕ)).X n :=
  ∑ i : Fin (n + 1),
    x i ≫ A.ιTotal (down ℕ) i.1 (n - i.1) n (totalAntidiagonalDegree n i)

/-- Helper for Chap10 Lemma 10 75 3: project a total-degree object to one fixed
antidiagonal summand. -/
noncomputable def totalAntidiagonalProjection
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    (n : ℕ) (i : Fin (n + 1)) :
    (A.total (down ℕ)).X n ⟶ (A.X i.1).X (n - i.1) :=
  A.totalDesc (fun p q _ ↦
    if hpq : p = i.1 ∧ q = n - i.1 then
      (HomologicalComplex₂.XXIsoOfEq (ModuleCat R) (down ℕ) (down ℕ) A
        hpq.1 hpq.2).hom
    else
      0)

/-- Helper for Chap10 Lemma 10 75 3: the antidiagonal projection has the expected value on
each total summand. -/
private theorem ιTotal_totalAntidiagonalProjection
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    (p q n : ℕ) (h : ComplexShape.π (down ℕ) (down ℕ) (down ℕ) (p, q) = n)
    (i : Fin (n + 1)) :
    A.ιTotal (down ℕ) p q n h ≫ totalAntidiagonalProjection A n i =
      if hpq : p = i.1 ∧ q = n - i.1 then
        (HomologicalComplex₂.XXIsoOfEq (ModuleCat R) (down ℕ) (down ℕ) A
          hpq.1 hpq.2).hom
      else
        0 := by
  -- This is the defining computation rule for `totalDesc` specialized to the chosen summand.
  rw [totalAntidiagonalProjection, HomologicalComplex₂.ι_totalDesc]

/-- Helper for Chap10 Lemma 10 75 3: an assembled antidiagonal map projects back to each
component. -/
private theorem totalAntidiagonalLift_projection
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    {T : ModuleCat R} (n : ℕ)
    (x : ∀ i : Fin (n + 1), T ⟶ (A.X i.1).X (n - i.1)) (i : Fin (n + 1)) :
    totalAntidiagonalLift A n x ≫ totalAntidiagonalProjection A n i = x i := by
  -- After composing the finite sum with the projection, every summand except `i` vanishes.
  unfold totalAntidiagonalLift
  rw [Preadditive.sum_comp]
  rw [Finset.sum_eq_single i]
  · rw [Category.assoc, ιTotal_totalAntidiagonalProjection]
    simp
  · intro j _ hj
    rw [Category.assoc, ιTotal_totalAntidiagonalProjection]
    have hpq : ¬ (j.1 = i.1 ∧ n - j.1 = n - i.1) := by
      intro hpair
      exact hj (Fin.ext hpair.1)
    simp [hpq]
  · intro hi
    simp at hi

/-- Helper for Chap10 Lemma 10 75 3: moving one step along the finite antidiagonal preserves the
expected complementary vertical degree. -/
theorem antidiagonalSuccVertical_eq
    (n : ℕ) {m : ℕ} (i : Fin (m + 1)) :
    n + 1 - i.succ.1 = n - i.castSucc.1 := by
  -- The successor raises the horizontal degree by one, while `castSucc` forgets the ambient
  -- bound without changing the underlying horizontal coordinate.
  have hsucc : i.succ.1 = i.1 + 1 := by
    simp
  have hcast : i.castSucc.1 = i.1 := by
    simp
  omega

/-- Helper for Chap10 Lemma 10 75 3: the row-cokernel component of an antidiagonal lift is
the horizontal-degree-zero component. -/
theorem totalAntidiagonalLift_totalToRowCokernelComponent
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    {T : ModuleCat R} (n : ℕ)
    (x : ∀ i : Fin (n + 1), T ⟶ (A.X i.1).X (n - i.1)) :
    totalAntidiagonalLift A n x ≫ totalToRowCokernelComponent A n =
      x ⟨0, Nat.succ_pos n⟩ ≫ cokernel.π ((A.d 1 0).f n) := by
  -- Compose the finite sum with the row comparison and keep only the horizontal-degree-zero
  -- summand; all positive horizontal summands are killed by the component formula.
  unfold totalAntidiagonalLift
  rw [Preadditive.sum_comp]
  rw [Finset.sum_eq_single (⟨0, Nat.succ_pos n⟩ : Fin (n + 1))]
  · rw [Category.assoc, ιTotal_totalToRowCokernelComponent]
    simp
  · intro i _ hi
    rw [Category.assoc, ιTotal_totalToRowCokernelComponent]
    have hval : (i : ℕ) ≠ 0 := by
      intro hzero
      exact hi (Fin.ext hzero)
    simp [hval]
  · intro hnot
    simp at hnot

/-- Helper for Chap10 Lemma 10 75 3: the unique antidiagonal family in total degree `0` is
determined by its single component in `A_{0,0}`. -/
def degreeZeroAntidiagonalFamily
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    {T : ModuleCat R} (a₀ : T ⟶ (A.X 0).X 0) :
    ∀ i : Fin 1, T ⟶ (A.X i.1).X (0 - i.1)
  | 0 => a₀

/-- Helper for Chap10 Lemma 10 75 3: the total-degree-`1` antidiagonal family is determined by
its `(0,1)` and `(1,0)` components. -/
def degreeOneAntidiagonalFamily
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    {T : ModuleCat R} (b₀ : T ⟶ (A.X 0).X 1) (a₁ : T ⟶ (A.X 1).X 0) :
    ∀ i : Fin 2, T ⟶ (A.X i.1).X (1 - i.1)
  | 0 => b₀
  | 1 => a₁

/-- Helper for Chap10 Lemma 10 75 3: maps into a finite coproduct are determined by the
standard additive projections from that coproduct. -/
private theorem sigmaProjection_ext {ι : Type*} [DecidableEq ι]
    {F : ι → ModuleCat R} [HasBiproduct F] {T : ModuleCat R}
    {f g : T ⟶ ∐ F} (h : ∀ i, f ≫ Sigma.π F i = g ≫ Sigma.π F i) :
    f = g := by
  -- Move the comparison to the chosen biproduct, where the projections are jointly monic.
  apply (cancel_mono (biproduct.isoCoproduct F).inv).1
  apply biproduct.hom_ext
  intro i
  have hπ : (biproduct.isoCoproduct F).inv ≫ biproduct.π F i = Sigma.π F i := by
    -- The inverse from the coproduct to the biproduct has the standard projection components.
    apply Sigma.hom_ext
    intro j
    by_cases hji : j = i
    · subst j
      rw [biproduct.isoCoproduct_inv, Sigma.ι_desc_assoc,
        biproduct.ι_π_self, Sigma.ι_π_eq_id]
    · rw [biproduct.isoCoproduct_inv, Sigma.ι_desc_assoc,
        biproduct.ι_π_ne F hji, Sigma.ι_π_of_ne F hji]
  rw [Category.assoc, Category.assoc, hπ]
  exact h i

/-- Helper for Chap10 Lemma 10 75 3: a raw pair on the total-degree `n` antidiagonal has a
finite horizontal coordinate. -/
private theorem totalDegreeFirst_lt_succ
    {n : ℕ} (pq : {pq : ℕ × ℕ //
      ComplexShape.π (down ℕ) (down ℕ) (down ℕ) pq ∈ ({n} : Set ℕ)}) :
    pq.1.1 < n + 1 := by
  -- The total-degree equation is `p + q = n`, so the first coordinate is at most `n`.
  have hpq : pq.1.1 + pq.1.2 = n := by
    simpa [ComplexShape.π] using pq.2
  omega

/-- Helper for Chap10 Lemma 10 75 3: the custom antidiagonal projection is the standard
`Sigma.π` projection from the coproduct defining the total object. -/
private theorem totalAntidiagonalProjection_sigmaπ
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    (n : ℕ) (i : Fin (n + 1)) :
    totalAntidiagonalProjection A n i =
      Sigma.π (A.toGradedObject.mapObjFun
        (ComplexShape.π (down ℕ) (down ℕ) (down ℕ)) n)
        ⟨(i.1, n - i.1), totalAntidiagonalDegree n i⟩ := by
  -- Compare after every total summand inclusion, where both maps have the same Kronecker delta.
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  rw [ιTotal_totalAntidiagonalProjection]
  by_cases hpqi : p = i.1 ∧ q = n - i.1
  · obtain ⟨rfl, rfl⟩ := hpqi
    have hidx :
        (⟨(i.1, n - i.1), hpq⟩ :
          ↑((ComplexShape.π (down ℕ) (down ℕ) (down ℕ)) ⁻¹' ({n} : Set ℕ))) =
        ⟨(i.1, n - i.1), totalAntidiagonalDegree n i⟩ := by
      apply Subtype.ext
      rfl
    have hσ := Sigma.ι_π
      (A.toGradedObject.mapObjFun (ComplexShape.π (down ℕ) (down ℕ) (down ℕ)) n)
      (⟨(i.1, n - i.1), hpq⟩ :
        ↑((ComplexShape.π (down ℕ) (down ℕ) (down ℕ)) ⁻¹' ({n} : Set ℕ)))
      (⟨(i.1, n - i.1), totalAntidiagonalDegree n i⟩ :
        ↑((ComplexShape.π (down ℕ) (down ℕ) (down ℕ)) ⁻¹' ({n} : Set ℕ)))
    rw [HomologicalComplex₂.ιTotal, GradedObject.ιMapObj]
    erw [hσ]
    simp [hidx, GradedObject.mapObjFun, HomologicalComplex₂.toGradedObject]
  · have hidx :
        (⟨(p, q), hpq⟩ :
          ↑((ComplexShape.π (down ℕ) (down ℕ) (down ℕ)) ⁻¹' ({n} : Set ℕ))) ≠
        ⟨(i.1, n - i.1), totalAntidiagonalDegree n i⟩ := by
      intro h
      apply hpqi
      constructor
      · exact congrArg (fun x ↦ x.1.1) h
      · exact congrArg (fun x ↦ x.1.2) h
    have hσ := Sigma.ι_π_of_ne
      (A.toGradedObject.mapObjFun (ComplexShape.π (down ℕ) (down ℕ) (down ℕ)) n) hidx
    simpa [hpqi, HomologicalComplex₂.ιTotal, GradedObject.ιMapObj] using hσ.symm

/-- Helper for Chap10 Lemma 10 75 3: the finite antidiagonal projections are jointly monic
for maps into a fixed total degree. -/
theorem totalAntidiagonalProjection_ext
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    {T : ModuleCat R} {n : ℕ} {f g : T ⟶ (A.total (down ℕ)).X n}
    (h : ∀ i : Fin (n + 1),
      f ≫ totalAntidiagonalProjection A n i =
        g ≫ totalAntidiagonalProjection A n i) :
    f = g := by
  -- The raw fiber of pairs with total degree `n` is equivalent to the finite antidiagonal
  -- `Fin (n+1)`, so the coproduct defining total degree `n` is a finite biproduct.
  classical
  let e :
      ↑((ComplexShape.π (down ℕ) (down ℕ) (down ℕ)) ⁻¹' ({n} : Set ℕ)) ≃
        Fin (n + 1) := {
    toFun pq := ⟨pq.1.1, totalDegreeFirst_lt_succ pq⟩
    invFun i := ⟨(i.1, n - i.1), totalAntidiagonalDegree n i⟩
    left_inv pq := by
      rcases pq with ⟨⟨p, q⟩, hpq⟩
      apply Subtype.ext
      dsimp
      have hpq' : p + q = n := by
        simpa [ComplexShape.π] using hpq
      apply Prod.ext
      · rfl
      · omega
    right_inv i := by
      apply Fin.ext
      rfl }
  haveI :
      Fintype ↑((ComplexShape.π (down ℕ) (down ℕ) (down ℕ)) ⁻¹' ({n} : Set ℕ)) :=
    Fintype.ofEquiv (Fin (n + 1)) e.symm
  haveI :
      Finite ↑((ComplexShape.π (down ℕ) (down ℕ) (down ℕ)) ⁻¹' ({n} : Set ℕ)) :=
    Finite.of_fintype _
  haveI : HasFiniteBiproducts (ModuleCat R) := inferInstance
  haveI :
      HasBiproductsOfShape
        ↑((ComplexShape.π (down ℕ) (down ℕ) (down ℕ)) ⁻¹' ({n} : Set ℕ))
        (ModuleCat R) :=
    hasBiproductsOfShape_finite (ModuleCat R)
  haveI : HasBiproduct
      (A.toGradedObject.mapObjFun (ComplexShape.π (down ℕ) (down ℕ) (down ℕ)) n) :=
    HasBiproductsOfShape.has_biproduct _
  -- After rewriting custom projections to `Sigma.π`, finite-coproduct extensionality applies.
  apply sigmaProjection_ext
  intro pq
  rcases pq with ⟨⟨p, q⟩, hpq⟩
  have hpq' : p + q = n := by
    simpa [ComplexShape.π] using hpq
  have hp : p < n + 1 := by omega
  have hq : q = n - p := by omega
  subst q
  let i : Fin (n + 1) := ⟨p, hp⟩
  have hidx :
      (⟨(p, n - p), hpq⟩ :
        ↑((ComplexShape.π (down ℕ) (down ℕ) (down ℕ)) ⁻¹' ({n} : Set ℕ))) =
      ⟨(i.1, n - i.1), totalAntidiagonalDegree n i⟩ := by
    apply Subtype.ext
    rfl
  simpa [totalAntidiagonalProjection_sigmaπ A n i, i, hidx] using h i

/-- Helper for Chap10 Lemma 10 75 3: the summand `(j + 1, n + 1 - (j + 1))` lies in total degree
`n + 1`. -/
private theorem succAntidiagonalTotalDegree
    (n : ℕ) (j : Fin (n + 1)) :
    ComplexShape.π (down ℕ) (down ℕ) (down ℕ) (j.succ.1, n + 1 - j.succ.1) = n + 1 := by
  -- This is the tautological total-degree identity for the successor antidiagonal index.
  simp [ComplexShape.π]
  omega

/-- Helper for Chap10 Lemma 10 75 3: after one horizontal step, the adjacent antidiagonal summand
lies in total degree `n`. -/
private theorem castSuccAntidiagonalTotalDegree
    (n : ℕ) (j : Fin (n + 1)) :
    ComplexShape.π (down ℕ) (down ℕ) (down ℕ) (j.castSucc.1, n + 1 - j.succ.1) = n := by
  -- The cast-successor and successor indices differ by one, so the total degree drops by one.
  simp [ComplexShape.π]
  omega

/-- Helper for Chap10 Lemma 10 75 3: the summand `(j, n - j)` lies on the degree-`n`
antidiagonal. -/
private theorem antidiagonalTotalDegree
    (n : ℕ) (j : Fin (n + 1)) :
    ComplexShape.π (down ℕ) (down ℕ) (down ℕ) (j.1, n - j.1) = n := by
  -- This is the basic total-degree normalization for the degree-`n` antidiagonal.
  simp [ComplexShape.π]
  omega

/-- Helper for Chap10 Lemma 10 75 3: the horizontal differential connects adjacent horizontal
indices on the same antidiagonal. -/
private theorem succCastSuccRel
    (n : ℕ) (j : Fin (n + 1)) :
    (down ℕ).Rel j.succ.1 j.castSucc.1 := by
  -- In the `down ℕ` shape, successor and cast-successor differ by exactly one.
  simp [ComplexShape.down, ComplexShape.down']

/-- Helper for Chap10 Lemma 10 75 3: the vertical differential connects adjacent vertical indices
on successive antidiagonals. -/
private theorem antidiagonalVerticalRel
    (n : ℕ) (j : Fin (n + 1)) :
    (down ℕ).Rel (n + 1 - j.1) (n - j.1) := by
  -- Moving vertically lowers the second index by one.
  simp [ComplexShape.down, ComplexShape.down']
  omega

/-- Helper for Chap10 Lemma 10 75 3: a single horizontal total-differential summand projects to
the adjacent antidiagonal component. -/
private theorem singleHorizontalDifferential_projection
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    {T : ModuleCat R} (n : ℕ) (j i : Fin (n + 1))
    (x : T ⟶ (A.X j.succ.1).X (n + 1 - j.succ.1)) :
    (x ≫ A.ιTotal (down ℕ) j.succ.1 (n + 1 - j.succ.1) (n + 1)
        (succAntidiagonalTotalDegree n j) ≫
      A.D₁ (down ℕ) (n + 1) n) ≫ totalAntidiagonalProjection A n i =
      if hji : j = i then
        x ≫ (A.d j.succ.1 j.castSucc.1).f (n + 1 - j.succ.1) ≫
          (HomologicalComplex₂.XXIsoOfEq (ModuleCat R) (down ℕ) (down ℕ) A
            (by simpa [hji] using congrArg Fin.val hji)
            (by simpa [hji] using antidiagonalSuccVertical_eq n j)).hom
      else
        0 := by
  -- Route correction: rewrite the single `D₁` summand directly to the diagonal/off-diagonal
  -- projection formula before assembling finite sums.
  repeat rw [Category.assoc]
  rw [HomologicalComplex₂.ι_D₁_assoc]
  rw [A.d₁_eq (down ℕ) (succCastSuccRel n j) (n + 1 - j.succ.1) n
    (castSuccAntidiagonalTotalDegree n j)]
  simp only [ε₁_def, one_smul]
  by_cases hji : j = i
  · subst i
    have hpq : j.castSucc.1 = j.1 ∧ n + 1 - j.succ.1 = n - j.1 := by
      constructor
      · simp
      · simpa using antidiagonalSuccVertical_eq n j
    calc
      x ≫ (A.d j.succ.1 j.castSucc.1).f (n + 1 - j.succ.1) ≫
          A.ιTotal (down ℕ) j.castSucc.1 (n + 1 - j.succ.1) n
            (castSuccAntidiagonalTotalDegree n j) ≫
          totalAntidiagonalProjection A n j
        =
          x ≫ (A.d j.succ.1 j.castSucc.1).f (n + 1 - j.succ.1) ≫
            (A.ιTotal (down ℕ) j.castSucc.1 (n + 1 - j.succ.1) n
              (castSuccAntidiagonalTotalDegree n j) ≫
              totalAntidiagonalProjection A n j) := by
            simp
      _ =
          x ≫ (A.d j.succ.1 j.castSucc.1).f (n + 1 - j.succ.1) ≫
            (if hpq' : j.castSucc.1 = j.1 ∧ n + 1 - j.succ.1 = n - j.1 then
              (HomologicalComplex₂.XXIsoOfEq (ModuleCat R) (down ℕ) (down ℕ) A
                hpq'.1 hpq'.2).hom
            else
              0) := by
            rw [ιTotal_totalAntidiagonalProjection]
      _ = if hji : j = j then
            x ≫ (A.d j.succ.1 j.castSucc.1).f (n + 1 - j.succ.1) ≫
              (HomologicalComplex₂.XXIsoOfEq (ModuleCat R) (down ℕ) (down ℕ) A
                (by simpa [hji] using congrArg Fin.val hji)
                (by simpa [hji] using antidiagonalSuccVertical_eq n j)).hom
          else
            0 := by
            simp
  ·
    have hpq :
        ¬ (j.castSucc.1 = i.1 ∧ n + 1 - j.succ.1 = n - i.1) := by
      intro hpair
      apply hji
      apply Fin.ext
      simpa using hpair.1
    calc
      x ≫ (A.d j.succ.1 j.castSucc.1).f (n + 1 - j.succ.1) ≫
          A.ιTotal (down ℕ) j.castSucc.1 (n + 1 - j.succ.1) n
            (castSuccAntidiagonalTotalDegree n j) ≫
          totalAntidiagonalProjection A n i
        =
          x ≫ (A.d j.succ.1 j.castSucc.1).f (n + 1 - j.succ.1) ≫
            (A.ιTotal (down ℕ) j.castSucc.1 (n + 1 - j.succ.1) n
              (castSuccAntidiagonalTotalDegree n j) ≫
              totalAntidiagonalProjection A n i) := by
            simp
      _ =
          x ≫ (A.d j.succ.1 j.castSucc.1).f (n + 1 - j.succ.1) ≫
            (if hpq' : j.castSucc.1 = i.1 ∧ n + 1 - j.succ.1 = n - i.1 then
              (HomologicalComplex₂.XXIsoOfEq (ModuleCat R) (down ℕ) (down ℕ) A
                hpq'.1 hpq'.2).hom
            else
              0) := by
            rw [ιTotal_totalAntidiagonalProjection]
      _ = 0 := by
            have hpair : ¬ (j.1 = i.1 ∧ n - j.1 = n - i.1) := by
              intro h
              apply hji
              exact Fin.ext h.1
            simpa [hpair, Category.assoc] using
              (show
                x ≫ (A.d j.succ.1 j.castSucc.1).f (n + 1 - j.succ.1) ≫
                    (0 :
                      (A.X j.castSucc.1).X (n + 1 - j.succ.1) ⟶
                        (A.X i.1).X (n - i.1)) = 0 by
                rw [comp_zero, comp_zero])
      _ = if hji : j = i then
            x ≫ (A.d j.succ.1 j.castSucc.1).f (n + 1 - j.succ.1) ≫
              (HomologicalComplex₂.XXIsoOfEq (ModuleCat R) (down ℕ) (down ℕ) A
                (by simpa [hji] using congrArg Fin.val hji)
                (by simpa [hji] using antidiagonalSuccVertical_eq n j)).hom
          else
            0 := by
            simp [hji]

/-- Helper for Chap10 Lemma 10 75 3: a single vertical total-differential summand projects to
the same horizontal component on the adjacent antidiagonal, with the total-complex sign. -/
private theorem verticalProjectionMatch
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    (n : ℕ) (j : Fin (n + 1)) :
    A.ιTotal (down ℕ) j.1 (n - j.1) n
        (antidiagonalTotalDegree n j) ≫
      totalAntidiagonalProjection A n j =
        (HomologicalComplex₂.XXIsoOfEq (ModuleCat R) (down ℕ) (down ℕ) A
          (by simp)
          (by simp)).hom := by
  -- This is the diagonal specialization of the antidiagonal projection formula.
  simpa [ιTotal_totalAntidiagonalProjection]

/-- Helper for Chap10 Lemma 10 75 3: projecting a vertical summand to a different antidiagonal
component gives zero. -/
private theorem verticalProjectionMismatch
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    (n : ℕ) (j i : Fin (n + 1)) (hji : j ≠ i) :
    A.ιTotal (down ℕ) j.1 (n - j.1) n
        (antidiagonalTotalDegree n j) ≫
      totalAntidiagonalProjection A n i = 0 := by
  -- Off the diagonal, the defining `if` in the projection formula vanishes.
  have hpq : ¬ (j.1 = i.1 ∧ n - j.1 = n - i.1) := by
    intro hpair
    exact hji (Fin.ext hpair.1)
  simpa [ιTotal_totalAntidiagonalProjection, hpq]

/-- Helper for Chap10 Lemma 10 75 3: a single vertical total-differential summand projects to
the same horizontal component on the adjacent antidiagonal, with the total-complex sign. -/
private theorem singleVerticalDifferential_projection
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    {T : ModuleCat R} (n : ℕ) (j i : Fin (n + 1))
    (x : T ⟶ (A.X j.1).X (n + 1 - j.1)) :
    (x ≫ A.ιTotal (down ℕ) j.1 (n + 1 - j.1) (n + 1)
        (by
          simp [ComplexShape.π]) ≫
      A.D₂ (down ℕ) (n + 1) n) ≫ totalAntidiagonalProjection A n i =
      if hji : j = i then
        x ≫ (ComplexShape.ε₂ (down ℕ) (down ℕ) (down ℕ) (j.1, n + 1 - j.1) •
          (A.X j.1).d (n + 1 - j.1) (n - j.1)) ≫
          (HomologicalComplex₂.XXIsoOfEq (ModuleCat R) (down ℕ) (down ℕ) A
            (by simpa [hji] using congrArg Fin.val hji)
            (by simpa [hji] using congrArg (fun k : ℕ ↦ n - k) (congrArg Fin.val hji))).hom
      else
        0 := by
  -- Route correction: normalize the single projected `D₂` summand first, then let the diagonal
  -- and off-diagonal projection lemmas decide whether the surviving `ιTotal` term is an isomorphism
  -- or zero.
  repeat rw [Category.assoc]
  rw [HomologicalComplex₂.ι_D₂_assoc]
  rw [A.d₂_eq (down ℕ) j.1 (antidiagonalVerticalRel n j) n (antidiagonalTotalDegree n j)]
  rw [← Category.assoc]
  erw [Linear.comp_units_smul]
  erw [Linear.units_smul_comp]
  by_cases hji : j = i
  · subst i
    -- On the diagonal, the projected `ιTotal` summand is the canonical antidiagonal isomorphism.
    simpa [Category.assoc] using
      congrArg
        (fun f ↦
          ComplexShape.ε₂ (down ℕ) (down ℕ) (down ℕ) (j.1, n + 1 - j.1) •
            (x ≫ (A.X j.1).d (n + 1 - j.1) (n - j.1) ≫ f))
        (verticalProjectionMatch A n j)
  · -- Off the diagonal, the projected `ιTotal` summand vanishes.
    simpa [Category.assoc, hji] using
      congrArg
        (fun f ↦
          ComplexShape.ε₂ (down ℕ) (down ℕ) (down ℕ) (j.1, n + 1 - j.1) •
            (x ≫ (A.X j.1).d (n + 1 - j.1) (n - j.1) ≫ f))
        (verticalProjectionMismatch A n j i hji)

/-- Helper for Chap10 Lemma 10 75 3: the horizontal part of the total differential of an
antidiagonal lift has the expected projection to each target antidiagonal summand. -/
private theorem totalAntidiagonalLift_D₁_projection
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    {T : ModuleCat R} (n : ℕ)
    (x : ∀ i : Fin (n + 2), T ⟶ (A.X i.1).X (n + 1 - i.1)) (i : Fin (n + 1)) :
    (totalAntidiagonalLift A (n + 1) x ≫ A.D₁ (down ℕ) (n + 1) n) ≫
        totalAntidiagonalProjection A n i =
      x i.succ ≫ (A.d i.succ.1 i.castSucc.1).f (n + 1 - i.succ.1) ≫
        (HomologicalComplex₂.XXIsoOfEq (ModuleCat R) (down ℕ) (down ℕ) A
          (by simp)
          (antidiagonalSuccVertical_eq n i)).hom := by
  -- Split off the horizontal-degree-zero summand, which has no horizontal differential, and
  -- collapse the remaining finite sum to the unique surviving `i.succ` component.
  unfold totalAntidiagonalLift
  rw [Preadditive.sum_comp, Fin.sum_univ_succ, Preadditive.add_comp, Preadditive.sum_comp]
  have hzero :
      (((x (0 : Fin (n + 2)) ≫
          A.ιTotal (down ℕ) ↑(0 : Fin (n + 2))
            (n + 1 - ↑(0 : Fin (n + 2))) (n + 1)
            (totalAntidiagonalDegree (n + 1) 0)) ≫
        A.D₁ (down ℕ) (n + 1) n) ≫
          totalAntidiagonalProjection A n i) = 0 := by
    repeat rw [Category.assoc]
    rw [HomologicalComplex₂.ι_D₁_assoc]
    rw [A.d₁_eq_zero (down ℕ) ↑(0 : Fin (n + 2)) (n + 1 - ↑(0 : Fin (n + 2))) n
      (by
        simp [ComplexShape.down, ComplexShape.down'])]
    rw [zero_comp, comp_zero]
  rw [hzero, zero_add]
  rw [Finset.sum_eq_single i]
  · simpa using singleHorizontalDifferential_projection A n i i (x i.succ)
  · intro j _ hji
    simpa [hji] using singleHorizontalDifferential_projection A n j i (x j.succ)
  · intro hi
    simp at hi

/-- Helper for Chap10 Lemma 10 75 3: the vertical part of the total differential of an
antidiagonal lift has the expected projection to each target antidiagonal summand. -/
private theorem totalAntidiagonalLift_D₂_projection
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    {T : ModuleCat R} (n : ℕ)
    (x : ∀ i : Fin (n + 2), T ⟶ (A.X i.1).X (n + 1 - i.1)) (i : Fin (n + 1)) :
    (totalAntidiagonalLift A (n + 1) x ≫ A.D₂ (down ℕ) (n + 1) n) ≫
        totalAntidiagonalProjection A n i =
      x i.castSucc ≫
        (ComplexShape.ε₂ (down ℕ) (down ℕ) (down ℕ) (i.1, n + 1 - i.1) •
          (A.X i.1).d (n + 1 - i.1) (n - i.1)) := by
  -- Split off the vertical-degree-zero summand, which has no vertical differential, and
  -- collapse the remaining finite sum to the unique surviving `i.castSucc` component.
  unfold totalAntidiagonalLift
  rw [Preadditive.sum_comp, Fin.sum_univ_castSucc, Preadditive.add_comp, Preadditive.sum_comp]
  have hzero :
      (((x (Fin.last (n + 1)) ≫
          A.ιTotal (down ℕ) ↑(Fin.last (n + 1))
            (n + 1 - ↑(Fin.last (n + 1))) (n + 1)
            (totalAntidiagonalDegree (n + 1) (Fin.last (n + 1)))) ≫
        A.D₂ (down ℕ) (n + 1) n) ≫
          totalAntidiagonalProjection A n i) = 0 := by
    repeat rw [Category.assoc]
    rw [HomologicalComplex₂.ι_D₂_assoc]
    rw [A.d₂_eq_zero (down ℕ) ↑(Fin.last (n + 1))
      (n + 1 - ↑(Fin.last (n + 1))) n
      (by
        simp [ComplexShape.down, ComplexShape.down'])]
    rw [zero_comp, comp_zero]
  rw [hzero, add_zero]
  rw [Finset.sum_eq_single i]
  · simpa using singleVerticalDifferential_projection A n i i (x i.castSucc)
  · intro j _ hji
    simpa [hji] using singleVerticalDifferential_projection A n j i (x j.castSucc)
  · intro hi
    simp at hi

/-- Helper for Chap10 Lemma 10 75 3: postcomposing a total differential with one antidiagonal
projection splits into the projected horizontal and vertical total-differential parts. -/
private theorem projectedTotalDifferentialSplit
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    {T : ModuleCat R} (n : ℕ)
    (x : T ⟶ (A.total (down ℕ)).X (n + 1)) (i : Fin (n + 1)) :
    (x ≫ (A.total (down ℕ)).d (n + 1) n) ≫ totalAntidiagonalProjection A n i =
      (x ≫ A.D₁ (down ℕ) (n + 1) n) ≫ totalAntidiagonalProjection A n i +
        (x ≫ A.D₂ (down ℕ) (n + 1) n) ≫ totalAntidiagonalProjection A n i := by
  -- The total differential is defined as `D₁ + D₂`, so after one reassociation the projection
  -- sees the two summands separately.
  have hcomp :
      x ≫ (A.D₁ (down ℕ) (n + 1) n + A.D₂ (down ℕ) (n + 1) n) =
        x ≫ A.D₁ (down ℕ) (n + 1) n + x ≫ A.D₂ (down ℕ) (n + 1) n := by
    exact
      Preadditive.comp_add _ _ _ x (A.D₁ (down ℕ) (n + 1) n) (A.D₂ (down ℕ) (n + 1) n)
  have hpost :
      (x ≫ (A.D₁ (down ℕ) (n + 1) n + A.D₂ (down ℕ) (n + 1) n)) ≫
          totalAntidiagonalProjection A n i =
        (x ≫ A.D₁ (down ℕ) (n + 1) n + x ≫ A.D₂ (down ℕ) (n + 1) n) ≫
          totalAntidiagonalProjection A n i := by
    exact congrArg (fun f ↦ f ≫ totalAntidiagonalProjection A n i) hcomp
  calc
    (x ≫ (A.total (down ℕ)).d (n + 1) n) ≫ totalAntidiagonalProjection A n i =
      ((x ≫ A.D₁ (down ℕ) (n + 1) n) + (x ≫ A.D₂ (down ℕ) (n + 1) n)) ≫
        totalAntidiagonalProjection A n i := by
          rw [A.total_d]
          exact hpost
    _ =
      (x ≫ A.D₁ (down ℕ) (n + 1) n) ≫ totalAntidiagonalProjection A n i +
        (x ≫ A.D₂ (down ℕ) (n + 1) n) ≫ totalAntidiagonalProjection A n i := by
          exact
            Preadditive.add_comp _ _ _
              (x ≫ A.D₁ (down ℕ) (n + 1) n)
              (x ≫ A.D₂ (down ℕ) (n + 1) n)
              (totalAntidiagonalProjection A n i)

/-- Helper for Chap10 Lemma 10 75 3: the projection of the differential of an antidiagonal lift
is the expected horizontal-plus-vertical staircase relation. -/
private theorem totalAntidiagonalLift_d_projection
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    {T : ModuleCat R} (n : ℕ)
    (x : ∀ i : Fin (n + 2), T ⟶ (A.X i.1).X (n + 1 - i.1)) (i : Fin (n + 1)) :
    (totalAntidiagonalLift A (n + 1) x ≫ (A.total (down ℕ)).d (n + 1) n) ≫
        totalAntidiagonalProjection A n i =
      x i.succ ≫ (A.d i.succ.1 i.castSucc.1).f (n + 1 - i.succ.1) ≫
        (HomologicalComplex₂.XXIsoOfEq (ModuleCat R) (down ℕ) (down ℕ) A
          (by simp)
          (antidiagonalSuccVertical_eq n i)).hom +
      x i.castSucc ≫
          (ComplexShape.ε₂ (down ℕ) (down ℕ) (down ℕ) (i.1, n + 1 - i.1) •
            (A.X i.1).d (n + 1 - i.1) (n - i.1)) := by
  -- Route correction: split the projected total differential once, then reuse the already
  -- normalized `D₁` and `D₂` projection formulas without reopening the summand-level transport.
  rw [projectedTotalDifferentialSplit A n (totalAntidiagonalLift A (n + 1) x) i]
  rw [totalAntidiagonalLift_D₁_projection, totalAntidiagonalLift_D₂_projection]
  rfl

/-- Helper for Chap10 Lemma 10 75 3: every map into one total degree is recovered from its
finite antidiagonal projections. -/
private theorem totalMorph_eq_totalAntidiagonalLift
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    {T : ModuleCat R} (n : ℕ) (f : T ⟶ (A.total (down ℕ)).X n) :
    f = totalAntidiagonalLift A n (fun i ↦ f ≫ totalAntidiagonalProjection A n i) := by
  -- Compare both maps after every finite antidiagonal projection.
  apply totalAntidiagonalProjection_ext A
  intro i
  simpa using (totalAntidiagonalLift_projection A n
    (fun i ↦ f ≫ totalAntidiagonalProjection A n i) i).symm

/-- Helper for Chap10 Lemma 10 75 3: a staircase relation on every projected antidiagonal
component forces the assembled lift to be a total cycle. -/
theorem totalAntidiagonalLift_cycleOfStaircase
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    {T : ModuleCat R} (n : ℕ)
    (x : ∀ i : Fin (n + 2), T ⟶ (A.X i.1).X (n + 1 - i.1))
    (hx : ∀ i : Fin (n + 1),
      x i.succ ≫ (A.d i.succ.1 i.castSucc.1).f (n + 1 - i.succ.1) ≫
          (HomologicalComplex₂.XXIsoOfEq (ModuleCat R) (down ℕ) (down ℕ) A
            (by simp)
            (antidiagonalSuccVertical_eq n i)).hom +
        x i.castSucc ≫
          (ComplexShape.ε₂ (down ℕ) (down ℕ) (down ℕ) (i.1, n + 1 - i.1) •
            (A.X i.1).d (n + 1 - i.1) (n - i.1)) = 0) :
    totalAntidiagonalLift A (n + 1) x ≫ (A.total (down ℕ)).d (n + 1) n = 0 := by
  -- Compare after every finite antidiagonal projection; the staircase hypothesis is exactly the
  -- projected differential formula, and the projections are jointly monic.
  apply totalAntidiagonalProjection_ext A
  intro i
  rw [zero_comp, totalAntidiagonalLift_d_projection]
  exact hx i

/-- Helper for Chap10 Lemma 10 75 3: a total cycle yields the staircase relation on its
projected antidiagonal components. -/
private theorem projectedTotalCycle_staircase
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    {T : ModuleCat R} (n : ℕ)
    (x₂ : T ⟶ (A.total (down ℕ)).X (n + 1))
    (hx₂ : x₂ ≫ (A.total (down ℕ)).d (n + 1) n = 0)
    (i : Fin (n + 1)) :
    x₂ ≫ totalAntidiagonalProjection A (n + 1) i.succ ≫
        (A.d i.succ.1 i.castSucc.1).f (n + 1 - i.succ.1) ≫
          (HomologicalComplex₂.XXIsoOfEq (ModuleCat R) (down ℕ) (down ℕ) A
            (by simp)
            (antidiagonalSuccVertical_eq n i)).hom +
      x₂ ≫ totalAntidiagonalProjection A (n + 1) i.castSucc ≫
        (ComplexShape.ε₂ (down ℕ) (down ℕ) (down ℕ) (i.1, n + 1 - i.1) •
          (A.X i.1).d (n + 1 - i.1) (n - i.1)) = 0 := by
  -- Rewrite the total cycle through its antidiagonal lift decomposition, then project the
  -- differential with the staircase formula.
  have hproj :
      (x₂ ≫ (A.total (down ℕ)).d (n + 1) n) ≫ totalAntidiagonalProjection A n i = 0 := by
    simpa [Category.assoc] using
      congrArg (fun f ↦ f ≫ totalAntidiagonalProjection A n i) hx₂
  calc
    x₂ ≫ totalAntidiagonalProjection A (n + 1) i.succ ≫
        (A.d i.succ.1 i.castSucc.1).f (n + 1 - i.succ.1) ≫
          (HomologicalComplex₂.XXIsoOfEq (ModuleCat R) (down ℕ) (down ℕ) A
            (by simp)
            (antidiagonalSuccVertical_eq n i)).hom +
      x₂ ≫ totalAntidiagonalProjection A (n + 1) i.castSucc ≫
        (ComplexShape.ε₂ (down ℕ) (down ℕ) (down ℕ) (i.1, n + 1 - i.1) •
          (A.X i.1).d (n + 1 - i.1) (n - i.1)) =
      ((totalAntidiagonalLift A (n + 1)
          (fun j ↦ x₂ ≫ totalAntidiagonalProjection A (n + 1) j) ≫
            (A.total (down ℕ)).d (n + 1) n) ≫
          totalAntidiagonalProjection A n i) := by
            simpa [Category.assoc] using
              (totalAntidiagonalLift_d_projection A n
                (fun j ↦ x₂ ≫ totalAntidiagonalProjection A (n + 1) j) i).symm
  _ = (x₂ ≫ (A.total (down ℕ)).d (n + 1) n) ≫ totalAntidiagonalProjection A n i := by
        rw [← totalMorph_eq_totalAntidiagonalLift A (n + 1) x₂]
  _ = 0 := hproj

/-- Helper for Chap10 Lemma 10 75 3: the triangular sign exponent advances by `i + 1` along the
finite antidiagonal. -/
private theorem staircaseTwistExponent_succ
    (n : ℕ) (i : Fin (n + 1)) :
    i.succ.1 * (i.succ.1 + 1) / 2 =
      i.castSucc.1 * (i.castSucc.1 + 1) / 2 + (i.1 + 1) := by
  -- The two `Fin` coercions change only the ambient bounds, so the claim is the standard
  -- triangular-number increment `T(k + 1) = T(k) + (k + 1)`.
  have hsucc : i.succ.1 = i.1 + 1 := by
    simp
  have hcast : i.castSucc.1 = i.1 := by
    simp
  calc
    i.succ.1 * (i.succ.1 + 1) / 2
      = ((i.1 + 1) * (i.1 + 2)) / 2 := by
          simp
    _ = (i.1 * (i.1 + 1) + 2 * (i.1 + 1)) / 2 := by
          congr 1
          ring
    _ = i.1 * (i.1 + 1) / 2 + (2 * (i.1 + 1)) / 2 := by
          rw [Nat.add_div_of_dvd_right (Nat.two_dvd_mul_add_one i.1)]
    _ = i.castSucc.1 * (i.castSucc.1 + 1) / 2 + (i.1 + 1) := by
          simp

/-- Helper for Chap10 Lemma 10 75 3: the triangular sign twist converts the vertical staircase
sign into the negated successor coefficient. -/
private theorem rawZigzagSignCoefficient
    (n : ℕ) (i : Fin (n + 1)) :
    -((((-1 : ℤˣ) ^ (i.castSucc.1 * (i.castSucc.1 + 1) / 2)) *
        ComplexShape.ε₂ (down ℕ) (down ℕ) (down ℕ) (i.1, n + 1 - i.1))) =
      (-1 : ℤˣ) ^ (i.succ.1 * (i.succ.1 + 1) / 2) := by
  have hε :
      ComplexShape.ε₂ (down ℕ) (down ℕ) (down ℕ) (i.1, n + 1 - i.1) =
        (-1 : ℤˣ) ^ i.1 := by
    simp [ε₂_def, ε_down_ℕ]
  rw [hε, neg_mul_eq_mul_neg]
  have hpow :
      -((-1 : ℤˣ) ^ i.1) = (-1 : ℤˣ) ^ (i.1 + 1) := by
    simpa using (pow_add (-1 : ℤˣ) i.1 1).symm
  have hpowadd :
      (-1 : ℤˣ) ^ (i.castSucc.1 * (i.castSucc.1 + 1) / 2) *
          (-1 : ℤˣ) ^ (i.1 + 1) =
        (-1 : ℤˣ) ^
          (i.castSucc.1 * (i.castSucc.1 + 1) / 2 + (i.1 + 1)) := by
    simpa using
      (pow_add (-1 : ℤˣ) (i.castSucc.1 * (i.castSucc.1 + 1) / 2) (i.1 + 1)).symm
  rw [hpow, hpowadd]
  simpa using congrArg (fun m ↦ (-1 : ℤˣ) ^ m) (staircaseTwistExponent_succ n i).symm

/-- Helper for Chap10 Lemma 10 75 3: the shifted inverse triangular twist absorbs the total
vertical sign on adjacent antidiagonal components. -/
theorem boundaryRawProjectionCoefficient
    (n : ℕ) (i : Fin (n + 1)) :
    (((-1 : ℤˣ) ^ ((i.succ.1 + 1) * (i.succ.1 + 2) / 2))⁻¹) *
      ComplexShape.ε₂ (down ℕ) (down ℕ) (down ℕ) (i.1, n + 1 - i.1) =
    (((-1 : ℤˣ) ^ ((i.castSucc.1 + 1) * (i.castSucc.1 + 2) / 2))⁻¹) := by
  have hshift :
      ((i.succ.1 + 1) * (i.succ.1 + 2) / 2) =
        ((i.castSucc.1 + 1) * (i.castSucc.1 + 2) / 2) + (i.1 + 2) := by
    simpa using staircaseTwistExponent_succ (n + 1) i.succ
  rw [hshift]
  have hpow :
      (-1 : ℤˣ) ^
          (((i.castSucc.1 + 1) * (i.castSucc.1 + 2) / 2) + (i.1 + 2)) *
          (-1 : ℤˣ) ^ i.1 =
        (-1 : ℤˣ) ^ ((i.castSucc.1 + 1) * (i.castSucc.1 + 2) / 2) := by
    have hpowadd :
        (-1 : ℤˣ) ^
            (((i.castSucc.1 + 1) * (i.castSucc.1 + 2) / 2) + (i.1 + 2)) =
          (-1 : ℤˣ) ^ ((i.castSucc.1 + 1) * (i.castSucc.1 + 2) / 2) *
            (-1 : ℤˣ) ^ (i.1 + 2) := by
      simpa using
        (pow_add (-1 : ℤˣ) ((i.castSucc.1 + 1) * (i.castSucc.1 + 2) / 2) (i.1 + 2))
    rw [hpowadd, mul_assoc]
    have hcancel :
        (-1 : ℤˣ) ^ (i.1 + 2) * (-1 : ℤˣ) ^ i.1 = 1 := by
      have hpow2 :
          (-1 : ℤˣ) ^ (i.1 + 2) = (-1 : ℤˣ) ^ i.1 * (-1 : ℤˣ) ^ 2 := by
        simpa [add_comm, add_left_comm, add_assoc] using (pow_add (-1 : ℤˣ) i.1 2)
      rw [hpow2]
      simp [pow_two]
    rw [hcancel, mul_one]
  simpa [ε₂_def, ε_down_ℕ] using hpow

/-- Helper for Chap10 Lemma 10 75 3: an unsigned zig-zag becomes a total-complex staircase after
the standard triangular sign twist. -/
theorem rawZigzagSignTwist
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    {T : ModuleCat R} (n : ℕ)
    (z : ∀ i : Fin (n + 2), T ⟶ (A.X i.1).X (n + 1 - i.1))
    (hz : ∀ i : Fin (n + 1),
      z i.succ ≫ (A.d i.succ.1 i.castSucc.1).f (n + 1 - i.succ.1) ≫
          (HomologicalComplex₂.XXIsoOfEq (ModuleCat R) (down ℕ) (down ℕ) A
            (by simp)
            (antidiagonalSuccVertical_eq n i)).hom =
        z i.castSucc ≫ (A.X i.1).d (n + 1 - i.1) (n - i.1)) :
    ∀ i : Fin (n + 1),
      (((-1 : ℤˣ) ^ (i.succ.1 * (i.succ.1 + 1) / 2)) • z i.succ) ≫
          (A.d i.succ.1 i.castSucc.1).f (n + 1 - i.succ.1) ≫
            (HomologicalComplex₂.XXIsoOfEq (ModuleCat R) (down ℕ) (down ℕ) A
            (by simp)
            (antidiagonalSuccVertical_eq n i)).hom +
        (((-1 : ℤˣ) ^ (i.castSucc.1 * (i.castSucc.1 + 1) / 2)) • z i.castSucc) ≫
          (ComplexShape.ε₂ (down ℕ) (down ℕ) (down ℕ) (i.1, n + 1 - i.1) •
            (A.X i.1).d (n + 1 - i.1) (n - i.1)) = 0 := by
  intro i
  -- Route correction: push both scalars onto the common vertical defect first, so the final step
  -- is just coefficient cancellation against `rawZigzagSignCoefficient`.
  let u : ℤˣ :=
    ((-1 : ℤˣ) ^ (i.castSucc.1 * (i.castSucc.1 + 1) / 2)) *
      ComplexShape.ε₂ (down ℕ) (down ℕ) (down ℕ) (i.1, n + 1 - i.1)
  let c : T ⟶ (A.X i.1).X (n - i.1) :=
    z i.castSucc ≫ (A.X i.1).d (n + 1 - i.1) (n - i.1)
  calc
    (((-1 : ℤˣ) ^ (i.succ.1 * (i.succ.1 + 1) / 2)) • z i.succ) ≫
        (A.d i.succ.1 i.castSucc.1).f (n + 1 - i.succ.1) ≫
          (HomologicalComplex₂.XXIsoOfEq (ModuleCat R) (down ℕ) (down ℕ) A
            (by simp)
            (antidiagonalSuccVertical_eq n i)).hom +
      (((-1 : ℤˣ) ^ (i.castSucc.1 * (i.castSucc.1 + 1) / 2)) • z i.castSucc) ≫
        (ComplexShape.ε₂ (down ℕ) (down ℕ) (down ℕ) (i.1, n + 1 - i.1) •
          (A.X i.1).d (n + 1 - i.1) (n - i.1)) =
      (((-1 : ℤˣ) ^ (i.succ.1 * (i.succ.1 + 1) / 2)) •
          (z i.succ ≫ (A.d i.succ.1 i.castSucc.1).f (n + 1 - i.succ.1) ≫
            (HomologicalComplex₂.XXIsoOfEq (ModuleCat R) (down ℕ) (down ℕ) A
              (by simp)
              (antidiagonalSuccVertical_eq n i)).hom)) +
        (u • c) := by
            repeat rw [← Category.assoc]
            erw [Linear.units_smul_comp, Linear.units_smul_comp]
            erw [Linear.units_smul_comp, Linear.comp_units_smul]
            simp [u, c, smul_smul]
    _ = 0 := by
          have hu :
              -u = ((-1 : ℤˣ) ^ (i.succ.1 * (i.succ.1 + 1) / 2)) := by
                dsimp [u]
                simpa using rawZigzagSignCoefficient n i
          rw [hz i, ← hu]
          have hcancel :
              -(u • (z i.castSucc ≫ (A.X i.1).d (n + 1 - i.1) (n - i.1))) +
                  u • (z i.castSucc ≫ (A.X i.1).d (n + 1 - i.1) (n - i.1)) = 0 :=
            neg_add_cancel (u • (z i.castSucc ≫ (A.X i.1).d (n + 1 - i.1) (n - i.1)))
          have hcancel0 :
              (-u) • z i.castSucc ≫ (A.X i.1).d (n + 1 - i.1) (n - i.1) +
                  u • z i.castSucc ≫ (A.X i.1).d (n + 1 - i.1) (n - i.1) = 0 := by
            simpa [c] using hcancel
          exact hcancel0

/-- Helper for Chap10 Lemma 10 75 3: in total degree `0`, the row comparison component is the
unique antidiagonal projection followed by the cokernel map. -/
theorem totalDegreeZeroComponent_eq_projection
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    {T : ModuleCat R} (x : T ⟶ (A.total (down ℕ)).X 0) :
    x ≫ totalToRowCokernelComponent A 0 =
      (show T ⟶ (A.X 0).X 0 from x ≫ totalAntidiagonalProjection A 0 0) ≫
        cokernel.π ((A.d 1 0).f 0) := by
  -- Degree zero has a single antidiagonal summand, so `totalToRowCokernelComponent` just reads
  -- that summand and applies the defining cokernel projection.
  calc
    x ≫ totalToRowCokernelComponent A 0 =
        totalAntidiagonalLift A 0 (fun i ↦ x ≫ totalAntidiagonalProjection A 0 i) ≫
          totalToRowCokernelComponent A 0 := by
            simpa [Category.assoc] using
              congrArg (fun f ↦ f ≫ totalToRowCokernelComponent A 0)
                (totalMorph_eq_totalAntidiagonalLift A 0 x)
    _ =
        (show T ⟶ (A.X 0).X 0 from x ≫ totalAntidiagonalProjection A 0 0) ≫
          cokernel.π ((A.d 1 0).f 0) := by
            simpa [Category.assoc] using
              (totalAntidiagonalLift_totalToRowCokernelComponent A 0
                (fun i ↦ x ≫ totalAntidiagonalProjection A 0 i))

/-- Helper for Chap10 Lemma 10 75 3: in every total degree, the row comparison component is the
horizontal-degree-zero antidiagonal projection followed by the cokernel map. -/
theorem totalToRowCokernelComponent_eq_headProjection
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    {T : ModuleCat R} (n : ℕ) (x : T ⟶ (A.total (down ℕ)).X n) :
    x ≫ totalToRowCokernelComponent A n =
      (show T ⟶ (A.X 0).X n from x ≫ totalAntidiagonalProjection A n 0) ≫
        cokernel.π ((A.d 1 0).f n) := by
  -- Rewrite the given map through its finite antidiagonal lift, then keep only the head
  -- component in the row-cokernel comparison.
  calc
    x ≫ totalToRowCokernelComponent A n =
        totalAntidiagonalLift A n (fun i ↦ x ≫ totalAntidiagonalProjection A n i) ≫
          totalToRowCokernelComponent A n := by
            simpa [Category.assoc] using
              congrArg (fun f ↦ f ≫ totalToRowCokernelComponent A n)
                (totalMorph_eq_totalAntidiagonalLift A n x)
    _ =
        (show T ⟶ (A.X 0).X n from x ≫ totalAntidiagonalProjection A n 0) ≫
          cokernel.π ((A.d 1 0).f n) := by
            simpa [Category.assoc] using
              (totalAntidiagonalLift_totalToRowCokernelComponent A n
                (fun i ↦ x ≫ totalAntidiagonalProjection A n i))

/-- Helper for Chap10 Lemma 10 75 3: the subtraction identity used in the zig-zag staircase
depends only on the underlying value of the finite index. -/
theorem succSub_castSucc_eq
    (n : ℕ) {m : ℕ} (i : Fin (m + 1)) :
    n + 1 - i.succ.1 = n - i.castSucc.1 := by
  -- Both `succ` and `castSucc` preserve the underlying natural-number coordinate up to the
  -- expected `+1`, so the complementary vertical degree shifts by one.
  have hsucc : i.succ.1 = i.1 + 1 := by
    simp
  have hcast : i.castSucc.1 = i.1 := by
    simp
  omega

/-- Helper for Chap10 Lemma 10 75 3: extending a finite family by one new last entry rewrites the
old successor indices as cast-successors of the smaller family. -/
theorem castSuccSucc_eq_succCastSucc
    {m : ℕ} (i : Fin (m + 1)) :
    i.castSucc.succ = i.succ.castSucc := by
  ext
  simp

/-- Helper for Chap10 Lemma 10 75 3: the successor of the old last index is the new last index. -/
private theorem lastSucc_eq_last
    (m : ℕ) :
    (Fin.last m).succ = Fin.last (m + 1) := by
  ext
  simp

/-- Helper for Chap10 Lemma 10 75 3: extend an antidiagonal family by one new last entry while
keeping the old entries in the cast-successor spelling. -/
def extendAntidiagonalFamily
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    {T T' : ModuleCat R} {m N : ℕ}
    (σ : T' ⟶ T)
    (z : ∀ i : Fin (m + 2), T ⟶ (A.X i.1).X (N - i.1))
    (w : T' ⟶ (A.X (m + 2)).X (N - (m + 2))) :
    ∀ i : Fin (m + 3), T' ⟶ (A.X i.1).X (N - i.1) :=
  fun i ↦ Fin.lastCases w (fun j ↦ σ ≫ z j) i

/-- Helper for Chap10 Lemma 10 75 3: the extended antidiagonal family agrees with the old family
on cast-successor indices. -/
theorem extendAntidiagonalFamily_castSucc
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    {T T' : ModuleCat R} {m N : ℕ}
    (σ : T' ⟶ T)
    (z : ∀ i : Fin (m + 2), T ⟶ (A.X i.1).X (N - i.1))
    (w : T' ⟶ (A.X (m + 2)).X (N - (m + 2)))
    (i : Fin (m + 2)) :
    extendAntidiagonalFamily A σ z w i.castSucc = σ ≫ z i := by
  -- The `castSucc` branch is exactly the non-last branch of `Fin.lastCases`.
  simp [extendAntidiagonalFamily]

/-- Helper for Chap10 Lemma 10 75 3: the extended antidiagonal family takes the prescribed value
at the new last index. -/
theorem extendAntidiagonalFamily_last
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    {T T' : ModuleCat R} {m N : ℕ}
    (σ : T' ⟶ T)
    (z : ∀ i : Fin (m + 2), T ⟶ (A.X i.1).X (N - i.1))
    (w : T' ⟶ (A.X (m + 2)).X (N - (m + 2))) :
    extendAntidiagonalFamily A σ z w (Fin.last (m + 2)) = w := by
  -- The last index of the enlarged family is the designated new branch.
  simp [extendAntidiagonalFamily]

/-- Helper for Chap10 Lemma 10 75 3: the staircase transport is exactly the bicomplex
commutativity square after normalizing the adjacent antidiagonal degree. -/
theorem staircaseTransport_comm
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    (n : ℕ) {m : ℕ} (i : Fin (m + 1)) :
    (A.d i.succ.1 i.castSucc.1).f (n + 1 - i.succ.1) ≫
        (HomologicalComplex₂.XXIsoOfEq (ModuleCat R) (down ℕ) (down ℕ) A
          (by simp)
          (succSub_castSucc_eq n i)).hom ≫
        (A.X i.1).d (n - i.1) (n - i.succ.1) =
      (A.X i.succ.1).d (n + 1 - i.succ.1) (n - i.succ.1) ≫
        (A.d i.succ.1 i.castSucc.1).f (n - i.succ.1) := by
  cases' i with i hi
  by_cases hrel : (down ℕ).Rel (n + 1 - (i + 1)) (n - (i + 1))
  · have hrel' : (down ℕ).Rel (n - i) (n - (i + 1)) := by
      simpa [ComplexShape.down, ComplexShape.down'] using hrel
    have htransport :
        eqToHom (by simp) ≫ (A.X i).d (n - i) (n - (i + 1)) =
          (A.X i).d (n + 1 - (i + 1)) (n - (i + 1)) := by
      -- In the genuine `down`-relation case, the two source degrees differ only by the
      -- canonical predecessor equality, so `eqToHom_comp_d` removes the transport.
      simpa [ComplexShape.down, ComplexShape.down'] using
        (A.X i).eqToHom_comp_d
          (i := n + 1 - (i + 1)) (i' := n - i) (j := n - (i + 1))
          hrel hrel'
    -- Once the transport is removed, the claim is just the bicomplex commutativity square.
    simpa [HomologicalComplex₂.XXIsoOfEq] using
      (calc
        (A.d (i + 1) i).f (n + 1 - (i + 1)) ≫
            eqToHom (by simp) ≫ (A.X i).d (n - i) (n - (i + 1))
          =
            (A.d (i + 1) i).f (n + 1 - (i + 1)) ≫
              (A.X i).d (n + 1 - (i + 1)) (n - (i + 1)) := by
                simpa [Category.assoc] using
                  congrArg (fun f ↦ (A.d (i + 1) i).f (n + 1 - (i + 1)) ≫ f) htransport
        _ =
            (A.X (i + 1)).d (n + 1 - (i + 1)) (n - (i + 1)) ≫
              (A.d (i + 1) i).f (n - (i + 1)) := by
                simpa using (A.d_comm (i + 1) i (n + 1 - (i + 1)) (n - (i + 1))))
  · have hrel' : ¬ (down ℕ).Rel (n - i) (n - (i + 1)) := by
      simpa [ComplexShape.down, ComplexShape.down'] using hrel
    -- Outside the `down` shape, both vertical differentials vanish, so the square is trivial.
    have hleft :
        (A.X i).d (n - i) (n - (i + 1)) = 0 := (A.X i).shape _ _ hrel'
    have hright :
        (A.X i).d (n + 1 - (i + 1)) (n - (i + 1)) = 0 := (A.X i).shape _ _ hrel
    have hrightSucc :
        (A.X (i + 1)).d (n + 1 - (i + 1)) (n - (i + 1)) = 0 := (A.X (i + 1)).shape _ _ hrel
    simp [HomologicalComplex₂.XXIsoOfEq, hleft, hrightSucc]

end
