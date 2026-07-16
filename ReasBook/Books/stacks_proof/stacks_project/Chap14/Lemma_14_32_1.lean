import Mathlib
import stacks_proof.stacks_project.Chap14.Definition_14_30_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite Simplicial
open SSet.modelCategoryQuillen

universe u

variable {V U : SSet.{u}} (f : V ⟶ U)

/- Domain-style sampling for Lemma 14.32.1:
- primary domain: simplicial-set lifting properties and coskeletality.
- inspected owner declarations:
  `SSet.modelCategoryQuillen.I.rlp`,
  `SimplicialObject.IsCoskeletal`,
  `SimplicialObject.isCoskeletal_iff_isIso`,
  `SimplicialObject.isoCoskOfIsCoskeletal`.
- best owner abstractions:
  `I.rlp` for the textbook phrase “trivial Kan fibration”, and `IsCoskeletal n` for the
  coskeletality hypotheses.
- primitive-vs-derived split:
  primitive data: the morphism `f`, degreewise bijectivity below `n`, surjectivity in degree `n`,
  and the owner-level coskeletality assumptions on source and target;
  derived API: the source-facing phrase “trivial Kan fibration” for `I.rlp`, together with the
  canonical bridge from `IsCoskeletal n` to the unit isomorphism `X ≅ (cosk n).obj X`.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma that these degreewise hypotheses force a trivial Kan
  fibration;
- `core/canonical`: `I.rlp f` and the owner predicate `IsCoskeletal n`;
- `bridge/view`: `SimplicialObject.isCoskeletal_iff_isIso` and
  `SimplicialObject.isoCoskOfIsCoskeletal`.

There is no better upstream owner theorem to recall directly here; the correct refinement is to
keep the source-facing implication but express both the conclusion and the coskeletality input
through the canonical owners already used elsewhere in the chapter. -/

-- Proof sketch: to prove the boundary lifting property, consider a lifting problem against
-- `∂Δ[k].ι` and split into the cases `k ≤ n` and `k > n`. For `k ≤ n`, use surjectivity in
-- degree `n` together with degreewise bijectivity below `n` to construct a filler compatible with
-- the prescribed boundary. For `k > n`, use the `n`-coskeletality of `V` and `U` to identify
-- `k`-simplices with compatible `n`-skeletal boundary data, so the boundary datum determines a
-- unique filler.
/-- Helper for Lemma 14.32.1: each codimension-one face of `Δ[n + 1]` factors through the
boundary. -/
private theorem stdSimplex_face_le_boundary (n : ℕ) (j : Fin (n + 2)) :
    SSet.stdSimplex.face {j}ᶜ ≤ SSet.boundary (n + 1) := by
  -- The boundary is the supremum of all codimension-one faces, so each individual face includes
  -- into it.
  rw [SSet.boundary_eq_iSup]
  exact le_iSup (fun i : Fin (n + 2) ↦ SSet.stdSimplex.face {i}ᶜ) j

/-- Helper for Lemma 14.32.1: the range of the `j`-th codimension-one face map lies in the
boundary. -/
private theorem stdSimplex_face_range_le_boundary (n : ℕ) (j : Fin (n + 2)) :
    Subfunctor.range (SSet.stdSimplex.δ j) ≤ SSet.boundary (n + 1) := by
  -- Rewrite the face range into the standard subcomplex description and apply the previous lemma.
  simpa [SSet.stdSimplex.range_δ] using stdSimplex_face_le_boundary (n := n) j

/-- Helper for Lemma 14.32.1: the `j`-th codimension-one face of the boundary simplex
`∂Δ[n + 1]`. -/
private def boundary_face (n : ℕ) (j : Fin (n + 2)) :
    Δ[n] ⟶ (∂Δ[n + 1] : SSet.{u}) :=
  Subfunctor.lift (SSet.stdSimplex.δ j) (stdSimplex_face_range_le_boundary (n := n) j)

/-- Helper for Lemma 14.32.1: composing the boundary face inclusion with the boundary embedding
recovers the standard face map. -/
@[simp, reassoc]
private theorem boundary_face_ι (n : ℕ) (j : Fin (n + 2)) :
    boundary_face n j ≫ (∂Δ[n + 1]).ι = SSet.stdSimplex.δ j := by
  -- The lifted face map is defined precisely by factoring `stdSimplex.δ j` through the boundary.
  simp [boundary_face]

/-- Helper for Lemma 14.32.1: morphisms out of a boundary simplex are determined by their
restrictions to the codimension-one faces. -/
private theorem boundary_hom_ext {n : ℕ} {S : SSet.{u}} (σ₁ σ₂ : (∂Δ[n + 1] : SSet.{u}) ⟶ S)
    (h :
      ∀ j : Fin (n + 2),
        boundary_face n j ≫ σ₁ = boundary_face n j ≫ σ₂) :
    σ₁ = σ₂ := by
  -- As in the horn case, it suffices to check equality on the codimension-one face subcomplexes
  -- that generate the boundary.
  rw [← Subfunctor.equalizer_eq_iff]
  refine le_antisymm (Subfunctor.equalizer_le σ₁ σ₂) ?_
  simpa [SSet.boundary_eq_iSup] using
    (show (⨆ j : Fin (n + 2), SSet.stdSimplex.face {j}ᶜ) ≤ Subfunctor.equalizer σ₁ σ₂ from by
      simp only [iSup_le_iff]
      intro j
      rw [← SSet.stdSimplex.ofSimplex_yonedaEquiv_δ]
      rw [SSet.Subcomplex.ofSimplex_le_iff]
      refine (Subfunctor.mem_equalizer_iff σ₁ σ₂ (SSet.yonedaEquiv (boundary_face n j))).2 ?_
      -- Convert equality of morphisms `Δ[n] ⟶ S` into equality of the corresponding simplices.
      simpa [SSet.yonedaEquiv_comp] using congrArg SSet.yonedaEquiv (h j))

/-- Helper for Lemma 14.32.1: surjectivity in degree `n` together with bijectivity in all lower
degrees implies surjectivity on `0`-simplices. -/
private theorem zero_surjective_of_bijective_below_of_surjective
    (n : ℕ)
    (hbelow : ∀ i < n, Function.Bijective (f.app (op ⦋i⦌)))
    (hsurj : Function.Surjective (f.app (op ⦋n⦌))) :
    Function.Surjective (f.app (op ⦋0⦌)) := by
  -- Split into the source proof's cases `n = 0` and `0 < n`.
  cases n with
  | zero =>
      simpa using hsurj
  | succ n =>
      exact (hbelow 0 (Nat.succ_pos _)).2

/-- Helper for Lemma 14.32.1: below the top degree, every simplex of `Δ[k]` already lies in the
boundary, so the boundary inclusion is degreewise bijective there. -/
private theorem boundary_app_bijective_of_lt
    (k i : ℕ) (hi : i < k) :
    Function.Bijective (((∂Δ[k]).ι).app (op ⦋i⦌)) := by
  constructor
  · intro x y h
    exact Subtype.ext h
  · intro x
    -- Any `i`-simplex of `Δ[k]` is non-surjective when `i < k`, hence belongs to the boundary.
    refine ⟨⟨x, ?_⟩, rfl⟩
    intro hs
    have hcard := Fintype.card_le_of_surjective _ hs
    have hcard' : k ≤ i := by
      simpa using hcard
    exact Nat.not_le_of_lt hi hcard'

/-- Helper for Lemma 14.32.1: if `n < k`, then truncation identifies the boundary inclusion
`∂Δ[k] ⟶ Δ[k]` with an isomorphism, because all simplices in degrees `≤ n` already lie in the
boundary. -/
private theorem boundary_truncation_map_isIso_of_lt
    (n k : ℕ) (hk : n < k) :
    IsIso ((SSet.truncation n).map ((∂Δ[k]).ι)) := by
  -- Check the truncation componentwise, where it is just the lower-degree boundary inclusion.
  refine (NatTrans.isIso_iff_isIso_app _).2 ?_
  intro Δ
  cases Δ with
  | op Δ =>
      cases Δ with
      | mk Δ hΔ =>
          cases Δ with
          | mk i =>
              change IsIso (((∂Δ[k]).ι).app (op ⦋i⦌))
              rw [isIso_iff_bijective]
              exact boundary_app_bijective_of_lt (k := k) (i := i) (lt_of_le_of_lt hΔ hk)

/-- Helper for Lemma 14.32.1: in degrees `≤ n`, a boundary lifting problem is solved by lifting
the top simplex and then checking facewise compatibility in degree one lower, where `f` is
injective. -/
private theorem boundary_lifting_of_le
    (n m : ℕ)
    (hbelow : ∀ i < n, Function.Bijective (f.app (op ⦋i⦌)))
    (hsurj : Function.Surjective (f.app (op ⦋n⦌)))
    (hmn : m + 1 ≤ n) :
    HasLiftingProperty (∂Δ[m + 1].ι) f := by
  -- TODO: implement the low-degree source proof by lifting the top simplex in degree `m + 1`,
  -- then compare each codimension-one face after composing with `f`, and conclude with
  -- `boundary_hom_ext`.
  let _ := hbelow
  let _ := hsurj
  let _ := hmn
  sorry

/-- Helper for Lemma 14.32.1: above degree `n`, truncation turns the boundary inclusion into an
isomorphism, so the square has a unique truncated filler; coskeletality then transports that
truncated filler back to an actual simplex filler. -/
private theorem boundary_lifting_of_gt
    (n m : ℕ)
    (hbelow : ∀ i < n, Function.Bijective (f.app (op ⦋i⦌)))
    (hV : V.IsCoskeletal n)
    (hU : U.IsCoskeletal n)
    (hnm : n < m + 1) :
    HasLiftingProperty (∂Δ[m + 1].ι) f := by
  -- TODO: use the high-degree source proof in its stabilized adjunction form:
  -- (1) transport the lifting problem through `SSet.truncation n ⊣ SSet.Truncated.cosk n`,
  -- (2) solve the truncated square because `(SSet.truncation n).map (∂Δ[m + 1]).ι` is an
  -- isomorphism by `boundary_truncation_map_isIso_of_lt`, and
  -- (3) transport the resulting lift back across `V.isoCoskOfIsCoskeletal n` and
  -- `U.isoCoskOfIsCoskeletal n`.
  let _ := hbelow
  let _ := hV
  let _ := hU
  let _ := hnm
  sorry

/-- Lemma 14.32.1: a morphism of simplicial sets that is degreewise bijective in simplicial
degrees `< n`, surjective in degree `n`, and whose source and target are `n`-coskeletal is a
trivial Kan fibration, canonically expressed by the owner predicate `I.rlp`. -/
@[stacks 01A6]
theorem trivialKanFibration_of_bijective_below_of_surjective_of_coskeletal
    (n : ℕ)
    (hbelow : ∀ i < n, Function.Bijective (f.app (op ⦋i⦌)))
    (hsurj : Function.Surjective (f.app (op ⦋n⦌)))
    (hV : V.IsCoskeletal n)
    (hU : U.IsCoskeletal n) :
    I.rlp f := by
  -- Follow the source proof: prove surjectivity on `0`-simplices and then solve each boundary
  -- lifting problem by the split `k ≤ n` versus `k > n`.
  apply boundaryInclusions_rlp_of_zero_surjective_and_boundary_lifting
  · exact zero_surjective_of_bijective_below_of_surjective (f := f) n hbelow hsurj
  · intro m
    by_cases hmn : m + 1 ≤ n
    · exact boundary_lifting_of_le (f := f) n m hbelow hsurj hmn
    · exact boundary_lifting_of_gt (f := f) n m hbelow hV hU (lt_of_not_ge hmn)
