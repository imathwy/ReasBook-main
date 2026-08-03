module

public import Topology_Munkres_2000.Book.Remark_60_1.DegreeOneCharacters

public section

noncomputable section

namespace AlgebraicTopology

open CategoryTheory CategoryTheory.Limits

/-- Helper for Remark 60.1: an element of an integral module determines the
linear map from `ℤ` which sends one to that element. -/
def integerGeneratorMap (M : ModuleCat ℤ) (m : M) : ModuleCat.of ℤ ℤ ⟶ M :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ M m)

/-- Helper for Remark 60.1: the map from `ℤ` determined by `m` sends one to
`m`. -/
lemma integerGeneratorMap_apply_one (M : ModuleCat ℤ) (m : M) :
    integerGeneratorMap M m 1 = m := by
  -- Evaluate the canonical rank-one linear map on the integer generator.
  exact LinearMap.toSpanSingleton_apply_one ℤ M m

/-- Helper for Remark 60.1: the generator map of zero is the zero module
morphism. -/
lemma integerGeneratorMap_zero (M : ModuleCat ℤ) :
    integerGeneratorMap M 0 = 0 := by
  -- Evaluate both maps on an arbitrary integer scalar.
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  simp [integerGeneratorMap]

/-- Helper for Remark 60.1: generator maps preserve addition of their target
elements. -/
lemma integerGeneratorMap_add (M : ModuleCat ℤ) (m n : M) :
    integerGeneratorMap M (m + n) =
      integerGeneratorMap M m + integerGeneratorMap M n := by
  -- Evaluate both maps and distribute the integer action over addition.
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  simp [integerGeneratorMap, LinearMap.toSpanSingleton_apply]

/-- Helper for Remark 60.1: sending a coefficient to its map from the integer
generator is an additive homomorphism. -/
def integerGeneratorMapAddHom (M : ModuleCat ℤ) :
    M →+ (ModuleCat.of ℤ ℤ ⟶ M) :=
  { toFun := integerGeneratorMap M
    map_zero' := integerGeneratorMap_zero M
    map_add' := integerGeneratorMap_add M }

/-- Helper for Remark 60.1: integer scaling of a target element agrees with
scaling its generator map. -/
lemma integerGeneratorMap_zsmul (M : ModuleCat ℤ) (a : ℤ) (m : M) :
    integerGeneratorMap M (a • m) = a • integerGeneratorMap M m := by
  -- Additive homomorphisms commute with the canonical integer action.
  exact (integerGeneratorMapAddHom M).map_zsmul a m

/-- Helper for Remark 60.1: generator maps commute with finite sums. -/
lemma integerGeneratorMap_sum
    {ι : Type*} (M : ModuleCat ℤ) (s : Finset ι) (m : ι → M) :
    integerGeneratorMap M (∑ i ∈ s, m i) =
      ∑ i ∈ s, integerGeneratorMap M (m i) := by
  -- Induct over the finite support using the additive computation rules.
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, integerGeneratorMap_zero]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        integerGeneratorMap_add, ih]

/-- Helper for Remark 60.1: prescribed values on singular `n`-simplices extend
uniquely to a coefficient-valued singular cochain. -/
noncomputable def singularCochainOfSimplexValues
    (X : TopCat) (M : ModuleCat ℤ) (n : ℕ)
    (v : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)) → M) :
    singularCochainGroupWithCoefficients X M n :=
  ((TopCat.toSSet.obj X).isColimitChainComplexXCofan
      (ModuleCat.of ℤ ℤ) n).desc
    (Cofan.mk M (fun σ ↦ integerGeneratorMap M (v σ))) |>.hom

/-- Helper for Remark 60.1: composing a singular-simplex inclusion with the
cochain extended from simplex values gives the corresponding generator map. -/
lemma ιChainComplex_comp_singularCochainOfSimplexValues
    (X : TopCat) (M : ModuleCat ℤ) (n : ℕ)
    (v : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)) → M)
    (σ : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n))) :
    (TopCat.toSSet.obj X).ιChainComplex
        (R := ModuleCat.of ℤ ℤ) σ ≫
      ModuleCat.ofHom (singularCochainOfSimplexValues X M n v) =
    integerGeneratorMap M (v σ) := by
  -- This is the colimit computation rule for the defining coproduct descender.
  let targetCofan := Cofan.mk M (fun τ ↦ integerGeneratorMap M (v τ))
  exact ((TopCat.toSSet.obj X).isColimitChainComplexXCofan
    (ModuleCat.of ℤ ℤ) n).fac targetCofan (Discrete.mk σ)

/-- Helper for Remark 60.1: the cochain extended from simplex values has the
prescribed value on every singular-simplex generator. -/
lemma singularCochainOfSimplexValues_generator
    (X : TopCat) (M : ModuleCat ℤ) (n : ℕ)
    (v : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)) → M)
    (σ : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n))) :
    singularCochainOfSimplexValues X M n v
        ((TopCat.toSSet.obj X).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) σ |>.hom 1) = v σ := by
  -- The coproduct colimit computation reduces the generator to its prescribed
  -- rank-one map, whose value at one is the chosen coefficient.
  have hgenerator :=
    ιChainComplex_comp_singularCochainOfSimplexValues X M n v σ
  have hgeneratorOne := CategoryTheory.congr_fun hgenerator (1 : ℤ)
  exact hgeneratorOne.trans (integerGeneratorMap_apply_one M (v σ))

/-- Helper for Remark 60.1: simplex values satisfying the alternating
two-simplex face relation extend to a singular one-cocycle. -/
lemma singularCochainOfSimplexValues_isCocycle
    (X : TopCat) (M : ModuleCat ℤ)
    (v : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk 1)) → M)
    (hface : ∀ simplex : (TopCat.toSSet.obj X).obj
        (Opposite.op (SimplexCategory.mk 2)),
      ∑ i : Fin 3, ((-1 : ℤ) ^ i.val) •
        v ((TopCat.toSSet.obj X).δ i simplex) = 0) :
    ((singularCochainComplexWithCoefficients X M).d 1 2).hom
        (singularCochainOfSimplexValues X M 1 v) = 0 := by
  let cochainMap :
      ((TopCat.toSSet.obj X).chainComplex
        (ModuleCat.of ℤ ℤ)).X 1 ⟶ M :=
    ModuleCat.ofHom (singularCochainOfSimplexValues X M 1 v)
  have hboundary :
      ((TopCat.toSSet.obj X).chainComplex
        (ModuleCat.of ℤ ℤ)).d 2 1 ≫ cochainMap = 0 := by
    -- Singular two-chains are generated by two-simplices, so check the
    -- alternating boundary formula on one generator.
    apply SSet.chainComplex_hom_ext
    intro simplex
    rw [← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp,
      comp_zero]
    calc
      ∑ i : Fin 3, (((-1 : ℤ) ^ i.val) •
          (TopCat.toSSet.obj X).ιChainComplex
            ((TopCat.toSSet.obj X).δ i simplex)) ≫ cochainMap =
          ∑ i : Fin 3, integerGeneratorMap M
            (((-1 : ℤ) ^ i.val) •
              v ((TopCat.toSSet.obj X).δ i simplex)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Preadditive.zsmul_comp,
          ιChainComplex_comp_singularCochainOfSimplexValues,
          ← integerGeneratorMap_zsmul]
      _ = integerGeneratorMap M
          (∑ i : Fin 3, ((-1 : ℤ) ^ i.val) •
            v ((TopCat.toSSet.obj X).δ i simplex)) := by
        rw [integerGeneratorMap_sum]
      _ = 0 := by rw [hface simplex, integerGeneratorMap_zero]
  -- Translate the categorical boundary-composite equality back to the stored
  -- coefficient-valued coboundary.
  apply LinearMap.ext
  intro chain
  have hpoint := CategoryTheory.congr_fun hboundary chain
  rw [singularCochainComplexWithCoefficients_d_apply]
  exact hpoint

end AlgebraicTopology
