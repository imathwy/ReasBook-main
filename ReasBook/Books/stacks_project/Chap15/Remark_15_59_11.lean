import Mathlib
import stacks_project.Chap13.Lemma_13_13_8
import stacks_project.Chap13.Lemma_13_37_3
import stacks_project.Chap15.Lemma_15_79_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

open FilteredComplex
open FilteredCochainComplex

/-
Domain-style sampling for Remark 15.59.11:
- primary domain: filtered cochain-complex models and approximation towers for cochain complexes
  of `R`-modules and for the induced objects of the triangulated derived category `D(R)`;
- sampled owner declarations:
  `FilteredCochainComplex`,
  `FilteredCochainComplex.underlying`,
  `FilteredCochainComplex.stageMapOfLE`,
  `#check (∀ n : ℤ, IsSplitMono (α.f n))` from `Chap13/Definition_13_9_4`,
  `FilteredComplex`,
  `IsGeneratingFamilyApproximation`,
  `exists_generating_family_resolution`,
  `IsWeakGenerator`,
  `IsGeneratingFamily`,
  `ObjectProperty.IsTriangulated`,
  `ObjectProperty.IsClosedUnderIsomorphisms`,
  `ObjectProperty.IsClosedUnderColimitsOfShape`,
  `CategoryTheory.ringSingle`;
- best owner abstractions: `FilteredCochainComplex (ModuleCat R)` for the source-facing filtered
  witness together with an explicit quasi-isomorphism on its underlying complex, the underlying
  Chapter `12` owner `FilteredComplex (ModuleCat R)` as the core canonical model behind the
  `F^{p}` / `gr^{p}` surface, and the explicit recursive data of
  `exists_generating_family_resolution` together with
  `IsGeneratingFamilyApproximation (fun _ : Unit ↦ ringSingle) ...` for the induced
  distinguished-triangle resolution layer, and `IsWeakGenerator (ringSingle : DMod)` for the
  canonical object-level generation consequence;
- primitive data: a cochain complex `M`, a filtered cochain complex `F`, and a quasi-isomorphism
  `F.underlying ⟶ M`, where the negative-index stages encode the source increasing filtration
  `0 = F_{-1} ⊆ F_0 ⊆ F_1 ⊆ ⋯`, whose consecutive source inclusions are termwise split in the
  Chapter `13` sense `∀ n, IsSplitMono ((-).f n)`, and whose successive quotients are direct sums
  of shifts of the rank-one single complex;
- derived API: the generating-family resolution data in `D(R)`, the object-property consequence
  for arbitrary coproduct-stable triangulated properties, and the weak-generator reformulation;
- source/core/bridge triage:
  `source-facing`: the filtered-complex existence theorem below;
  `core/canonical`: the companion theorem `IsWeakGenerator (ringSingle : DMod)`;
  `bridge/view`: the generating-family resolution theorem and the object-property consequence,
    which translate the filtered witness into the chapter's triangulated owner vocabulary.

The previous version kept only the downstream object-property corollary. This file now restores
the source-facing filtered witness on the Chapter `15` owner
`FilteredCochainComplex (ModuleCat R)` and its induced distinguished-triangle resolution,
encoding the Stacks increasing filtration by the negative-index stages of the underlying canonical
owner `FilteredComplex`, and retains the object-property and weak-generator statements only as
companion consequences. -/

section

variable {R : Type u} [Ring R]

local notation "CpxMod" => CochainComplex (ModuleCat R) ℤ
local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "single" => CochainComplex.singleFunctor (ModuleCat R)

-- Proof sketch: build the approximation tower for the given complex `M`, take its colimit
-- `P^•`, and let the negative-index stages of the resulting filtered cochain complex encode the source
-- increasing filtration `0 = F_{-1} ⊆ F_0 ⊆ F_1 ⊆ ⋯`. The resulting comparison
-- `P^• ⟶ M^•` is a quasi-isomorphism, each component of every successor stage inclusion is split
-- mono, and the graded pieces are direct sums of shifts of the rank-one single complex.
/-- Remark 15.59.11: for every cochain complex `M^•` of `R`-modules there exists a
quasi-isomorphism `P^• ⟶ M^•` from a filtered cochain complex whose negative-index stages encode
an increasing filtration `0 = F_{-1}P^\bullet ⊆ F_0P^\bullet ⊆ F_1P^\bullet ⊆ ⋯` with union
`P^\bullet`, whose successor inclusions `F_iP^\bullet ⟶ F_{i + 1}P^\bullet` are termwise split,
i.e. each component map is a split monomorphism, and whose successive quotients
`F_iP^\bullet / F_{i - 1}P^\bullet` are direct sums of shifts of the one-term complex `R[k]`. In
the canonical decreasing owner `FilteredComplex`, the source stage `F_iP^\bullet` is encoded as
the stage `F^{-i} P^\bullet`. -/
theorem exists_splitFiltered_model_of_cochainComplex
    (M : CpxMod) :
    ∃ (P : FilteredCochainComplex (ModuleCat.{u} R)) (π : P.underlying ⟶ M),
      QuasiIso π ∧
      IsZero (F^{1} P) ∧
      (∀ n : ℤ, ((P.X n).filtration).IsExhaustive) ∧
      (∀ i : ℕ, ∀ n : ℤ,
        IsSplitMono
          ((P.stageMapOfLE
            (show -((i + 1 : ℕ) : ℤ) ≤ -((i : ℕ) : ℤ) by omega)).f n)) ∧
      (∀ i : ℕ,
        ∃ (J : Type u) (shift : J → ℤ),
          Nonempty
            (gr^{-((i : ℕ) : ℤ)} P ≅
              ∐ fun j : J ↦ (single (shift j)).obj ((ModuleCat.of R R) : ModuleCat.{u} R))) :=
  sorry

-- Proof sketch: choose a cochain-complex representative of `M`, apply the previous theorem, and
-- pass from the filtered model to the associated tower of negative-index stages in `D(R)`. The
-- graded-piece hypothesis identifies the initial term and all successive cones with direct sums of
-- shifts of `R[0]`, and the telescope triangle of the tower gives the distinguished triangle whose
-- homotopy colimit is `M`.
/-- Bridge/view form of Remark 15.59.11: every object of `D(R)` admits the Chapter `13`
generating-family resolution whose initial term and successive cone terms are direct sums of
shifts of `R[0]`, and whose canonical homotopy-colimit triangle resolves the object. -/
theorem exists_ringSingle_resolution
    [HasCoproducts DMod] (M : DMod) :
    ∃ (X : ℕ → DMod)
      (map : ∀ n : ℕ, X n ⟶ X (n + 1))
      (Y : ℕ → DMod)
      (triangleHom : ∀ n : ℕ, Y n ⟶ X n)
      (triangleConnecting : ∀ n : ℕ, X (n + 1) ⟶ (Y n)⟦(1 : ℤ)⟧)
      (Khocolim : DMod) (e : Khocolim ≅ M),
        IsGeneratingFamilyApproximation
            (fun _ : Unit ↦ (ringSingle : DMod))
            X map Y triangleHom triangleConnecting ∧
          IsHomotopyColimitOf (Functor.ofSequence map) Khocolim := by
  sorry

-- Proof sketch: apply the preceding generating-family resolution of `M`. The initial term and all
-- successive cone terms satisfy `T` by the shift and coproduct hypotheses, so repeated
-- two-out-of-three along the distinguished triangles of the resolution propagates `T` to every
-- stage and then to `M` through the telescope triangle.
/-- Companion consequence of Remark 15.59.11: let `T` be a property of objects of `D(R)`. If `T`
is preserved under arbitrary direct sums, satisfies the two-out-of-three property for
distinguished triangles, and holds for every shift `R[k]` of the ring object `R[0]`, then `T`
holds for every object of `D(R)`. -/
theorem objectProperty_on_all_derivedModules_of_coproducts_triangles_and_ring_shifts
    (T : ObjectProperty DMod) [∀ ι : Type u, T.IsClosedUnderColimitsOfShape (Discrete ι)]
    (htriangulated₁ :
      ∀ {Δ : Triangle DMod}, Δ ∈ distTriang DMod → T Δ.obj₂ → T Δ.obj₃ → T Δ.obj₁)
    (htriangulated₂ :
      ∀ {Δ : Triangle DMod}, Δ ∈ distTriang DMod → T Δ.obj₁ → T Δ.obj₃ → T Δ.obj₂)
    (htriangulated₃ :
      ∀ {Δ : Triangle DMod}, Δ ∈ distTriang DMod → T Δ.obj₁ → T Δ.obj₂ → T Δ.obj₃)
    (hshiftedRing : ∀ k : ℤ, T ((ringSingle : DMod)⟦k⟧)) : ∀ M : DMod, T M := sorry

-- Proof sketch: `ObjectProperty.IsTriangulated` only produces closure under distinguished
-- triangles up to `T.isoClosure`, so to recover the literal textbook hypotheses we also assume
-- `T` is closed under isomorphisms; then `ObjectProperty.ext_of_isTriangulatedClosedᵢ` gives the
-- three explicit two-out-of-three implications, and the source-facing theorem applies.
/-- Canonical triangulated-owner bridge for Remark 15.59.11: if `T` is stable under arbitrary
direct sums, is closed under isomorphisms, is a triangulated object property on `D(R)`, and holds
for every shift of `R[0]`, then `T` holds for every object of `D(R)`. -/
theorem objectProperty_on_all_derivedModules_of_coproducts_triangulated_and_ring_shifts
    (T : ObjectProperty DMod)
    [T.IsClosedUnderIsomorphisms] [T.IsTriangulated]
    [∀ ι : Type u, T.IsClosedUnderColimitsOfShape (Discrete ι)]
    (hshiftedRing : ∀ k : ℤ, T ((ringSingle : DMod)⟦k⟧)) : ∀ M : DMod, T M := by
  exact
    objectProperty_on_all_derivedModules_of_coproducts_triangles_and_ring_shifts T
      (fun hΔ h₂ h₃ ↦ T.ext_of_isTriangulatedClosed₁ _ hΔ h₂ h₃)
      (fun hΔ h₁ h₃ ↦ T.ext_of_isTriangulatedClosed₂ _ hΔ h₁ h₃)
      (fun hΔ h₁ h₂ ↦ T.ext_of_isTriangulatedClosed₃ _ hΔ h₁ h₂)
      hshiftedRing

-- Proof sketch: if `K` is right-orthogonal to all shifts of `R[0]`, let `A` be the shift-closure
-- of the singleton object property generated by `R[0]`. Then `K ∈ A.rightOrthogonal`, so the left
-- orthogonal `A.rightOrthogonal.leftOrthogonal` contains every shift of `R[0]`. This property is
-- triangulated and closed under arbitrary coproducts, hence the source-facing theorem shows it
-- contains every object, in particular `K`. Applying the defining left-orthogonality to
-- `𝟙 K : K ⟶ K` forces `K` to be zero.
/-- Canonical owner form of Remark 15.59.11: the degree-zero ring object `R[0]` is a weak
generator of the derived category `D(R)`. -/
theorem ringSingle_isWeakGenerator :
    IsWeakGenerator (ringSingle : DMod) := by
  rw [isWeakGenerator_iff_rightOrthogonal_shifts_eq_isZero]
  ext K
  constructor
  · intro hK
    let A : ObjectProperty DMod := (singleton (ringSingle : DMod)).shiftClosure ℤ
    have hAshifted :
        ∀ k : ℤ, A ((ringSingle : DMod)⟦k⟧) := fun k ↦
      ⟨(ringSingle : DMod), k, Iso.refl _, by simp⟩
    let P : ObjectProperty DMod := A.rightOrthogonal
    have hAorth : P K := by
      simpa [A, P] using hK
    let T : ObjectProperty DMod := P.leftOrthogonal
    letI : T.IsClosedUnderIsomorphisms := inferInstance
    letI : T.IsTriangulated := inferInstance
    letI (ι : Type u) : T.IsClosedUnderColimitsOfShape (Discrete ι) := by
      let hT : T = P.trW.isColocal := by
        simpa [T, P] using
          (show P.leftOrthogonal = P.trW.isColocal from
            (show P.trW.isColocal = P.leftOrthogonal from isColocal_trW P).symm)
      rw [hT]
      infer_instance
    have hTK : T K :=
      objectProperty_on_all_derivedModules_of_coproducts_triangulated_and_ring_shifts T
        (fun k ↦ by
          intro Y f hY
          exact hY f (hAshifted k)) K
    exact (Limits.IsZero.iff_id_eq_zero K).2 <| hTK (𝟙 K) hAorth
  · intro hK X f hX
    exact hK.eq_of_tgt f 0

end

end CategoryTheory
