import StacksProject_2024.Chap13.Definition_13_37_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe uA vA uB vB

section

variable {DA : Type uA} {DB : Type uB}
variable [Category.{vA} DA] [Category.{vB} DB]
variable [Preadditive DB] [Limits.HasCoproducts.{max uB vB} DB]
variable [HasShift DA ℤ] [HasShift DB ℤ]
variable (derivedTensorWithN : DA ⥤ DB)
variable (Aunit : DA) (N : DB)

-- Semantic recall hits: `Adjunction.fullyFaithfulLOfIsIsoUnit` gives the general
-- fully-faithful criterion for a left adjoint, and local precedent in Lemma `22.35.6` records
-- this compact/self-Ext derived-tensor argument as a theorem about a source-facing derived tensor
-- functor with a shifted free object.

/-- The shifted self-Ext comparison map induced by derived tensoring with `N`, a chosen
identification `derivedTensorWithN.obj Aunit ≅ N`, and chosen shifted identifications
`derivedTensorWithN.obj (Aunit[k]) ≅ N[k]`. -/
def tensorSelfExtMap
    (hTensorUnit : derivedTensorWithN.obj Aunit ≅ N)
    (hTensorShift :
      ∀ k : ℤ,
        derivedTensorWithN.obj ((shiftFunctor DA k).obj Aunit) ≅
          (shiftFunctor DB k).obj N)
    (k : ℤ) :
    (Aunit ⟶ (shiftFunctor DA k).obj Aunit) →
      (N ⟶ (shiftFunctor DB k).obj N) :=
  fun f ↦ hTensorUnit.inv ≫ derivedTensorWithN.map f ≫ (hTensorShift k).hom

@[simp]
theorem tensorSelfExtMap_apply
    (hTensorUnit : derivedTensorWithN.obj Aunit ≅ N)
    (hTensorShift :
      ∀ k : ℤ,
        derivedTensorWithN.obj ((shiftFunctor DA k).obj Aunit) ≅
          (shiftFunctor DB k).obj N)
    (k : ℤ)
    (f : Aunit ⟶ (shiftFunctor DA k).obj Aunit) :
    tensorSelfExtMap derivedTensorWithN Aunit N hTensorUnit hTensorShift k f =
      hTensorUnit.inv ≫ derivedTensorWithN.map f ≫ (hTensorShift k).hom :=
  rfl

/-- Lemma 22.33.7: with notation and assumptions as in Lemma `22.33.5`, let
`derivedTensorWithN = - ⊗_A^L N : D(A,d) ⥤ D(B,d)`. If `derivedTensorWithN` is a left
adjoint, `N` is a compact object of `D(B,d)`, and the natural map
`H^k(A) ≃ Hom_{D(A,d)}(A, A[k]) → Hom_{D(B,d)}(N, N[k])` induced by derived tensoring with `N`
is bijective for every `k`, then the induced map on every Hom-set is bijective, i.e.
`derivedTensorWithN` is fully faithful.

Here `Aunit` is the regular object `A` in `D(A,d)`, `hTensorUnit` identifies
`A ⊗_A^L N` with `N`, and `hTensorShift` records the standard identification
`A[k] ⊗_A^L N ≅ N[k]`. -/
@[stacks 09R9]
theorem derivedTensorWithN_fullyFaithful_of_compact_of_selfExt
    (hLeftAdjoint : Functor.IsLeftAdjoint derivedTensorWithN)
    (hTensorUnit : derivedTensorWithN.obj Aunit ≅ N)
    (hTensorShift :
      ∀ k : ℤ,
        derivedTensorWithN.obj ((shiftFunctor DA k).obj Aunit) ≅
          (shiftFunctor DB k).obj N)
    (hNCompact : IsCompactObject N)
    (hSelfExt :
      ∀ k : ℤ,
        Function.Bijective
          (tensorSelfExtMap derivedTensorWithN Aunit N hTensorUnit hTensorShift k))
    (X Y : DA) :
    Function.Bijective
      (derivedTensorWithN.map : (X ⟶ Y) → (derivedTensorWithN.obj X ⟶ derivedTensorWithN.obj Y)) :=
  by
    letI := hLeftAdjoint
    let hAdj : derivedTensorWithN ⊣ derivedTensorWithN.rightAdjoint :=
      Adjunction.ofIsLeftAdjoint derivedTensorWithN
    sorry

/-- Lemma `22.33.7` supplies the `Full` part of the fully-faithful conclusion. -/
instance derivedTensorWithN_full_of_compact_of_selfExt
    (hLeftAdjoint : Functor.IsLeftAdjoint derivedTensorWithN)
    (hTensorUnit : derivedTensorWithN.obj Aunit ≅ N)
    (hTensorShift :
      ∀ k : ℤ,
        derivedTensorWithN.obj ((shiftFunctor DA k).obj Aunit) ≅
          (shiftFunctor DB k).obj N)
    (hNCompact : IsCompactObject N)
    (hSelfExt :
      ∀ k : ℤ,
        Function.Bijective
          (tensorSelfExtMap derivedTensorWithN Aunit N hTensorUnit hTensorShift k)) :
    derivedTensorWithN.Full where
  map_surjective {X Y} :=
    (derivedTensorWithN_fullyFaithful_of_compact_of_selfExt
      derivedTensorWithN Aunit N hLeftAdjoint hTensorUnit hTensorShift
      hNCompact hSelfExt X Y).surjective

/-- Lemma `22.33.7` supplies the `Faithful` part of the fully-faithful conclusion. -/
instance derivedTensorWithN_faithful_of_compact_of_selfExt
    (hLeftAdjoint : Functor.IsLeftAdjoint derivedTensorWithN)
    (hTensorUnit : derivedTensorWithN.obj Aunit ≅ N)
    (hTensorShift :
      ∀ k : ℤ,
        derivedTensorWithN.obj ((shiftFunctor DA k).obj Aunit) ≅
          (shiftFunctor DB k).obj N)
    (hNCompact : IsCompactObject N)
    (hSelfExt :
      ∀ k : ℤ,
        Function.Bijective
          (tensorSelfExtMap derivedTensorWithN Aunit N hTensorUnit hTensorShift k)) :
    derivedTensorWithN.Faithful where
  map_injective {X Y} :=
    (derivedTensorWithN_fullyFaithful_of_compact_of_selfExt
      derivedTensorWithN Aunit N hLeftAdjoint hTensorUnit hTensorShift
      hNCompact hSelfExt X Y).injective

end
