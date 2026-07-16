import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
import Mathlib.CategoryTheory.Triangulated.Subcategory
import StacksProject_2024.stacks_project.Chap13.Lemma_13_10_7
import StacksProject_2024.stacks_project.Chap15.Definition_15_59_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_59_10

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open ComplexShape HomologicalComplex

noncomputable section

set_option checkBinderAnnotations false

universe u

namespace CochainComplex

section

variable {R : Type u} [CommRing R]
variable {K L : CochainComplex (ModuleCat R) ℤ}

local notation "KHom" => HomotopyCategory (ModuleCat R) (up ℤ)
local notation "Q" => HomotopyCategory.quotient (ModuleCat R) (up ℤ)

/- Domain sampling pass:
* primary domain: factorization up to homotopy of morphisms of cochain complexes of `R`-modules
  through quasi-isomorphisms with K-flat source, on the canonical tensor surface of
  `ModuleCat R`;
* sampled owner declarations:
  - `CochainComplex.IsKFlat` from `Definition_15_59_1`, the chapter owner for the K-flatness
    clause on the intermediate complex in the canonical module-tensor context;
  - `CochainComplex.tensorHom_right_quasiIso_of_isKFlat` from `Lemma_15_59_2`, the nearby owner
    showing that tensoring with a K-flat complex preserves quasi-isomorphisms;
  - `CochainComplex.isKFlat_obj₂_of_distinguished_triangle` and
    `CochainComplex.isKFlat_obj₃_of_distinguished_triangle` from `Lemma_15_59_5`, the chapter
    owners for the two-out-of-three propagation of K-flatness in distinguished triangles;
  - `exists_termwiseEpi_kFlatResolution` from `Lemma_15_59_10`, the chapter owner supplying the
    K-flat replacement input used in the standard construction;
  - `Homotopy` and `QuasiIso`, the canonical comparison owners for the factorization data.

Source/core/bridge triage:
* `source-facing`: the Stacks lemma is stated for an arbitrary ring, but the current Chapter 15
  owner `CochainComplex.IsKFlat` is available here only on the canonical tensor surface of
  `ModuleCat R`, so this file records the faithful commutative-ring specialization instead of
  quantifying over an arbitrary monoidal structure on `ModuleCat R`;
* `core/canonical`: `N.IsKFlat`, `QuasiIso c`, and `Homotopy a (b ≫ c)`;
* `bridge/view`: the commutative-ring specialization of the source factorization statement to the
  canonical module-tensor owner used in this chapter.

Primitive data are only the intermediate complex `N` and the maps `b`, `c`. The K-flatness,
quasi-isomorphism, and homotopy clauses are derived API over existing owner abstractions, so this
file exposes them directly instead of introducing a factorization wrapper structure.
-/

/-- Helper for Lemma 15.59.16: in a degreewise split short complex of cochain complexes of
`R`-modules, flatness of the outer terms forces flatness of the middle term. -/
lemma termwise_flat_of_degreewise_split
    {S : ShortComplex (CochainComplex (ModuleCat R) ℤ)}
    (σ : ∀ n : ℤ,
      (S.map (HomologicalComplex.eval (ModuleCat R) (up ℤ) n)).Splitting)
    (h₁ : S.X₁.IsTermwiseFlat) (h₃ : S.X₃.IsTermwiseFlat) :
    S.X₂.IsTermwiseFlat := by
  intro n
  -- Proof comment: the splitting in degree `n` identifies the middle term with the biproduct of
  -- the two outer terms in that degree.
  let e :
      S.X₂.X n ≅ (S.X₁.X n) ⊞ (S.X₃.X n) :=
    (σ n).isoBinaryBiproduct
  let eProd :
      S.X₂.X n ≅ ModuleCat.of R ((S.X₁.X n : Type u) × (S.X₃.X n : Type u)) :=
    e ≪≫ ModuleCat.biprodIsoProd _ _
  -- Proof comment: products of flat modules are flat, and flatness transports across the linear
  -- equivalence underlying the chosen splitting.
  let _ : Module.Flat R (S.X₁.X n : Type u) := h₁ n
  let _ : Module.Flat R (S.X₃.X n : Type u) := h₃ n
  let _ : Module.Flat R ((S.X₁.X n : Type u) × (S.X₃.X n : Type u)) := by
    infer_instance
  exact Module.Flat.of_linearEquiv eProd.toLinearEquiv

/-- Helper for Lemma 15.59.16: the source triangulated proof yields a factorization through a
degreewise split comparison triangle whose middle map to `L` is already a quasi-isomorphism. -/
lemma exists_degreewiseSplit_factorization_data
    (a : K ⟶ L) (hK : K.IsKFlat) :
    ∃ (M N : CochainComplex (ModuleCat R) ℤ)
      (π : M ⟶ CochainComplex.mappingCone a)
      (b : K ⟶ N) (g : N ⟶ M) (hbg : b ≫ g = 0)
      (σ : ∀ n : ℤ,
        ((ShortComplex.mk b g hbg).map
          (HomologicalComplex.eval (ModuleCat R) (up ℤ) n)).Splitting)
      (c : N ⟶ L),
      M.IsKFlat ∧ M.IsTermwiseFlat ∧ QuasiIso π ∧
        Nonempty (Homotopy a (b ≫ c)) ∧ N.IsKFlat ∧ QuasiIso c := by
  -- Proof comment: first resolve the cone of `a` by a K-flat, termwise-flat complex.
  obtain ⟨M, π, hM, hMFlat, hπ, _⟩ :=
    exists_termwiseEpi_kFlatResolution (R := R) (CochainComplex.mappingCone a)
  let δ : (Q.obj M) ⟶ (Q.obj K)⟦(1 : ℤ)⟧ :=
    Q.map π ≫ (CochainComplex.mappingCone.triangleh a).mor₃
  -- Proof comment: complete the composite `M ⟶ Cone(a) ⟶ K⟦1⟧` to a distinguished triangle in
  -- the homotopy category.
  obtain ⟨Y, bQ, gQ, hTδ⟩ := distinguished_cocone_triangle₂ δ
  -- Proof comment: replace the abstract middle vertex by an honest cochain complex whose short
  -- complex is degreewise split.
  obtain ⟨N, b, g, hbg, σ, e, he₁, he₃⟩ :=
    CategoryTheory.distinguished_triangle_iso_to_degreewiseSplit
      (A := K) (B := Y.as) (C := M) (a := bQ) (b := gQ) (c := δ) hTδ
  let S : ShortComplex (CochainComplex (ModuleCat R) ℤ) := ShortComplex.mk b g hbg
  let Tsplit : Triangle KHom := CochainComplex.trianglehOfDegreewiseSplit S σ
  have hTsplit : Tsplit ∈ distTriang KHom := by
    -- Proof comment: the split-model triangle is distinguished because it is isomorphic to the
    -- distinguished cocone triangle chosen above.
    exact isomorphic_distinguished _ hTδ _ e.symm
  have hTsplit_mor₃ : Tsplit.mor₃ = δ := by
    -- Proof comment: the comparison isomorphism is the identity on the first and third vertices,
    -- so it transports the connecting morphism without change.
    simpa [Tsplit, he₁, he₃] using e.hom.comm₃.symm
  have hN : N.IsKFlat := by
    -- Proof comment: K-flatness propagates to the middle term of the distinguished split-model
    -- triangle from the outer terms `K` and `M`.
    let P : CategoryTheory.ObjectProperty KHom := fun X ↦ X.IsKFlat
    exact
      P.ext_of_isTriangulatedClosed₂ Tsplit hTsplit
        (by simpa [Tsplit, S] using hK)
        (by simpa [Tsplit, S] using hM)
  let Tcone : Triangle KHom := CochainComplex.mappingCone.triangleh a
  have hTcone : Tcone ∈ distTriang KHom := by
    -- Proof comment: the mapping-cone triangle is the canonical distinguished triangle attached
    -- to `a`.
    simpa [Tcone] using HomotopyCategory.mappingCone_triangleh_distinguished a
  have hcomm₃ :
      Tsplit.mor₃ ≫ (𝟙 ((Q.obj K)⟦(1 : ℤ)⟧)) =
        Q.map π ≫ Tcone.mor₃ := by
    -- Proof comment: after identifying the split-model connecting morphism with `δ`, the third
    -- square is exactly the defining formula for `δ`.
    simp [Tsplit, Tcone, hTsplit_mor₃, δ, Category.assoc]
  -- Proof comment: `TR3` now fills in the middle map from the split-model triangle to the cone
  -- triangle.
  obtain ⟨cQ, hc₁, hc₂⟩ :=
    complete_distinguished_triangle_morphism₂
      Tsplit Tcone hTsplit hTcone (𝟙 (Q.obj K)) (Q.map π) hcomm₃
  obtain ⟨c, hcQ⟩ := Q.map_surjective cQ
  have hHom :
      Nonempty (Homotopy a (b ≫ c)) := by
    -- Proof comment: the first square of the triangle morphism identifies `Q.map (b ≫ c)` with
    -- `Q.map a`, which is exactly a homotopy in the quotient category.
    refine ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩
    calc
      Q.map a = Tcone.mor₁ := by simp [Tcone]
      _ = Tsplit.mor₁ ≫ cQ := by simpa using hc₁.symm
      _ = Q.map (b ≫ c) := by simp [Tsplit, S, hcQ]
  have hQπ :
      IsIso (Q.map π) := by
    have hπQ :
        HomotopyCategory.quasiIso (ModuleCat R) (up ℤ) (Q.map π) :=
      (HomotopyCategory.quotient_map_mem_quasiIso_iff
        (C := ModuleCat R) (c := up ℤ) π).2 hπ
    rw [HomotopyCategory.mem_quasiIso_iff] at hπQ
    exact hπQ
  let φ : Tsplit ⟶ Tcone :=
    Triangle.homMk _ _ (𝟙 (Q.obj K)) cQ (Q.map π) hc₁ hc₂ hcomm₃
  have hQcQ : IsIso cQ := by
    -- Proof comment: two-out-of-three for a morphism of distinguished triangles upgrades the
    -- middle component once the outer components are isomorphisms.
    simpa [φ] using
      (isIso₂_of_isIso₁₃ φ hTsplit hTcone (by infer_instance) hQπ : IsIso φ.hom₂)
  have hQc :
      HomotopyCategory.quasiIso (ModuleCat R) (up ℤ) (Q.map c) := by
    rw [hcQ]
    rw [HomotopyCategory.mem_quasiIso_iff]
    exact hQcQ
  have hc : QuasiIso c := by
    -- Proof comment: translate the isomorphism statement in the homotopy category back to a
    -- cochain-level quasi-isomorphism.
    exact
      (HomotopyCategory.quotient_map_mem_quasiIso_iff
        (C := ModuleCat R) (c := up ℤ) c).1 hQc
  exact ⟨M, N, π, b, g, hbg, σ, c, hM, hMFlat, hπ, hHom, hN, hc⟩

-- Proof sketch: complete `a` to a distinguished triangle and replace its cone by a K-flat
-- quasi-isomorphic model. The resulting comparison triangle
-- `K^• ⟶ N^• ⟶ M^• ⟶ K^•[1]` gives `N^•` K-flat by the two-out-of-three K-flatness theorem, and
-- the triangle comparison yields a map `c : N^• ⟶ L^•` whose composite with `b` is homotopic to
-- `a`.
/-- Commutative-ring specialization of Lemma 15.59.16 (1): if
`a : K^• ⟶ L^•` is a morphism of cochain complexes of `R`-modules and `K^•` is K-flat, then `a`
factors up to homotopy through a quasi-isomorphism `c : N^• ⟶ L^•` with `N^•` K-flat. -/
theorem exists_kFlat_factorization_up_to_homotopy
    (a : K ⟶ L) (hK : K.IsKFlat) :
    ∃ (N : CochainComplex (ModuleCat R) ℤ) (b : K ⟶ N) (c : N ⟶ L),
      Nonempty (Homotopy a (b ≫ c)) ∧ N.IsKFlat ∧ QuasiIso c := by
  -- Proof comment: unpack the split-model construction and forget the auxiliary cone resolution.
  rcases exists_degreewiseSplit_factorization_data (R := R) (K := K) (L := L) a hK with
    ⟨M, N, π, b, g, hbg, σ, c, hM, hMFlat, hπ, hHom, hN, hc⟩
  exact ⟨N, b, c, hHom, hN, hc⟩

/- The source also records a termwise-flat refinement. In the current Chapter 15 owner hierarchy,
`CochainComplex.IsTermwiseFlat` is likewise available on the commutative-ring tensor surface, so
the strengthened factorization theorem stays in the same canonical module-tensor context as the
preceding specialization. The source K-flatness hypothesis on `K` is retained here: termwise
flatness refines the choice of `N`, but the two-out-of-three K-flatness argument for `N` still
runs through `K.IsKFlat`. -/

-- Proof sketch: choose the comparison triangle in split degreewise form so that
-- `N^n ≅ M^n ⊕ K^n`; K-flatness of `K^•` and of the chosen cone replacement gives `N.IsKFlat`
-- by the same two-out-of-three argument as above, while flatness of the terms of `K^•` and of
-- the cone replacement propagates termwise to `N^•`.
/-- Commutative-ring bridge for the termwise-flat refinement of Lemma 15.59.16: if
`a : K^• ⟶ L^•` is a morphism of cochain
complexes of `R`-modules, `K^•` is K-flat, and each term of `K^•` is flat, then one may moreover
choose the intermediate complex `N^•` with flat terms. -/
theorem exists_termwiseFlat_kFlat_factorization_up_to_homotopy
    (a : K ⟶ L) (hK : K.IsKFlat) (hFlat : K.IsTermwiseFlat) :
    ∃ (N : CochainComplex (ModuleCat R) ℤ) (b : K ⟶ N) (c : N ⟶ L),
      Nonempty (Homotopy a (b ≫ c)) ∧ N.IsKFlat ∧ N.IsTermwiseFlat ∧ QuasiIso c := by
  -- Proof comment: use the same split-model factorization and read each degree of `N` as a split
  -- extension of the corresponding degrees of `K` and the termwise-flat cone resolution `M`.
  rcases exists_degreewiseSplit_factorization_data (R := R) (K := K) (L := L) a hK with
    ⟨M, N, π, b, g, hbg, σ, c, hM, hMFlat, hπ, hHom, hN, hc⟩
  let S : ShortComplex (CochainComplex (ModuleCat R) ℤ) := ShortComplex.mk b g hbg
  have hNFlat : N.IsTermwiseFlat := by
    -- Proof comment: degreewise splitness identifies `Nⁿ` with `Kⁿ ⊞ Mⁿ`, so flatness of `Kⁿ`
    -- and `Mⁿ` transports to `Nⁿ`.
    simpa [S] using
      termwise_flat_of_degreewise_split (R := R) (S := S) σ hFlat hMFlat
  exact ⟨N, b, c, hHom, hN, hNFlat, hc⟩

end

end CochainComplex
