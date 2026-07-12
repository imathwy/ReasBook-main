import StacksProject_2024.Chap22.Lemma_22_33_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

noncomputable section

universe uR uA vA uB vB

section

variable {R : Type uR} [CommRing R]
variable {DA : Type uA} {DB : Type uB}
variable [Category.{vA} DA] [Category.{vB} DB]
variable [HasZeroObject DA] [HasZeroObject DB]
variable [Preadditive DA] [Preadditive DB]
variable [CategoryTheory.Linear R DA] [CategoryTheory.Linear R DB]
variable [HasCoproducts.{max uB vB} DB]
variable [HasShift DA ℤ] [HasShift DB ℤ]
variable [∀ n : ℤ, (shiftFunctor DA n).Additive]
variable [∀ n : ℤ, (shiftFunctor DB n).Additive]
variable [Pretriangulated DA] [Pretriangulated DB]

variable (derivedTensorWithN : DA ⥤ DB) (derivedHomFromN : DB ⥤ DA)
variable [derivedTensorWithN.CommShift ℤ]
variable [derivedTensorWithN.IsTriangulated]
variable [derivedTensorWithN.Linear R]
variable (Aunit : DA) (N : DB)

-- Semantic recall hits: `Functor.IsEquivalence` is the canonical owner for an equivalence
-- induced by a functor, `Functor.kernel` records the right-adjoint zero-kernel criterion from
-- Lemma `13.7.2`, and local Chapter 13/22 precedent records compactness by
-- `IsCompactObject N`.

/-- The canonical comparison `derivedTensorWithN.obj (Aunit⟦k⟧) ≅ N⟦k⟧` induced by
`Functor.commShiftIso` and the chosen identification `derivedTensorWithN.obj Aunit ≅ N`. -/
def derivedTensorWithN_selfExtShiftIso
    (hTensorUnit : derivedTensorWithN.obj Aunit ≅ N)
    (k : ℤ) :
    derivedTensorWithN.obj (Aunit⟦k⟧) ≅ N⟦k⟧ :=
  ((derivedTensorWithN.commShiftIso k).app Aunit) ≪≫ (shiftFunctor DB k).mapIso hTensorUnit

/-- The canonical shifted self-Ext comparison map induced by derived tensoring with `N`. -/
def derivedTensorWithN_selfExtMap
    (hTensorUnit : derivedTensorWithN.obj Aunit ≅ N)
    (k : ℤ) :
    (Aunit ⟶ Aunit⟦k⟧) → (N ⟶ N⟦k⟧) :=
  tensorSelfExtMap derivedTensorWithN Aunit N hTensorUnit
    (derivedTensorWithN_selfExtShiftIso derivedTensorWithN Aunit N hTensorUnit) k

omit [HasZeroObject DA] [HasZeroObject DB] [HasCoproducts.{max uB vB} DB]
  [Preadditive DA] [Preadditive DB] [∀ n : ℤ, (shiftFunctor DA n).Additive]
  [∀ n : ℤ, (shiftFunctor DB n).Additive] [Pretriangulated DA] [Pretriangulated DB]
  [derivedTensorWithN.IsTriangulated] [derivedTensorWithN.Linear R] in
@[simp]
theorem derivedTensorWithN_selfExtMap_apply
    (hTensorUnit : derivedTensorWithN.obj Aunit ≅ N)
    (k : ℤ)
    (f : Aunit ⟶ Aunit⟦k⟧) :
    derivedTensorWithN_selfExtMap derivedTensorWithN Aunit N hTensorUnit k f =
      hTensorUnit.inv ≫
        derivedTensorWithN.map f ≫
          (derivedTensorWithN_selfExtShiftIso derivedTensorWithN Aunit N hTensorUnit k).hom :=
  rfl

/-- Lemma 22.37.2: let `R` be a ring, let `(A, d)` and `(B, d)` be differential graded
algebras over `R`, and let `N` be a differential graded `(A, B)`-bimodule. In the current
abstract derived-category surface, `DA` and `DB` denote `D(A, d)` and `D(B, d)`,
`derivedTensorWithN` denotes `- ⊗_A^L N`, `derivedHomFromN` denotes
`RHom(N, -)`, `Aunit` is the regular object `A`, and `N` is the corresponding object of
`DB`.

If `N` is compact in `DB`, the shifted Homs from `N` detect zero objects of `DB`, and the
canonical self-Ext maps
`Hom(Aunit, Aunit[k]) → Hom(N, N[k])` induced by derived tensoring with `N` are bijective for
all `k : ℤ`, then the derived tensor functor is an `R`-linear triangulated equivalence. The
hypothesis `hRHomZero_implies_hom_zero` records, at this abstract functor level, the standard
identification used in the Stacks proof that zero objects in the right-derived internal-Hom
functor have vanishing shifted Homs from `N`. The shift comparison
`derivedTensorWithN.obj (Aunit⟦k⟧) ≅ N⟦k⟧` is the canonical one obtained from
`derivedTensorWithN.commShiftIso k` and `hTensorUnit`. -/
@[stacks 09S7]
theorem derivedTensorWithN_isEquivalence_of_compact_detectsZero_selfExt
    (hAdj : derivedTensorWithN ⊣ derivedHomFromN)
    (hTensorUnit : derivedTensorWithN.obj Aunit ≅ N)
    (hNCompact : IsCompactObject N)
    (hDetectsZero :
      ∀ X : DB,
        (∀ n : ℤ, ∀ f : N ⟶ X⟦n⟧, f = 0) → IsZero X)
    (hRHomZero_implies_hom_zero :
      ∀ X : DB,
        IsZero (derivedHomFromN.obj X) →
          ∀ n : ℤ, ∀ f : N ⟶ X⟦n⟧, f = 0)
    (hSelfExt :
      ∀ k : ℤ,
        Function.Bijective
          (derivedTensorWithN_selfExtMap derivedTensorWithN Aunit N hTensorUnit k)) :
    derivedTensorWithN.IsEquivalence := sorry

end
