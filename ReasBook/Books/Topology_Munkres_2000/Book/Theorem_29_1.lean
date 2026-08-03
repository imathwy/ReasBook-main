module

public import Topology_Munkres_2000.Book.Definition_29_1.LocalCompactness
public import Mathlib.Topology.Category.CompHaus.Basic
public import Mathlib.Topology.Compactification.OnePoint.Basic

public section

open Set Topology

universe u v w

namespace OnePoint

/-- Theorem 29.1 (1): A space is locally compact Hausdorff exactly when it embeds in a compact
Hausdorff space with one-point complement. -/
theorem existsCompactification_iff {X : Type u} [TopologicalSpace X] :
    (WeaklyLocallyCompactSpace X ∧ T2Space X) ↔
      ∃ (Y : CompHaus.{u}) (f : X → Y) (y : Y),
        IsEmbedding f ∧ range f = {y}ᶜ := by
  constructor
  · rintro ⟨hlocal, hhausdorff⟩
    -- Equip the canonical one-point extension with its compact Hausdorff structure.
    letI : WeaklyLocallyCompactSpace X := hlocal
    letI : T2Space X := hhausdorff
    have hEmbedding : IsEmbedding ((↑) : X → OnePoint X) :=
      isOpenEmbedding_coe.isEmbedding
    have hRange : range ((↑) : X → OnePoint X) = {(∞ : OnePoint X)}ᶜ :=
      compl_infty.symm
    -- The coercion embeds `X`, and its complement is exactly the point at infinity.
    exact ⟨CompHaus.of (OnePoint X), (↑), ∞, hEmbedding, hRange⟩
  · rintro ⟨Y, f, y, hf, hy⟩
    -- A singleton complement makes the given embedding open.
    have hOpenRange : IsOpen (range f) := by
      rw [hy]
      exact isOpen_compl_singleton
    have hOpenEmbedding : IsOpenEmbedding f := ⟨hf, hOpenRange⟩
    -- Transport local compactness and Hausdorffness from the compact Hausdorff extension.
    letI : LocallyCompactSpace X := hOpenEmbedding.locallyCompactSpace
    exact ⟨inferInstance, hf.t2Space⟩

/-- The canonical homeomorphism between two compact Hausdorff one-point extensions of `X`. -/
noncomputable def compactificationEquiv {X : Type u} [TopologicalSpace X]
    (Y : CompHaus.{v}) (Y' : CompHaus.{w}) (f : X → Y) (f' : X → Y') (y : Y) (y' : Y')
    (hf : IsEmbedding f) (hf' : IsEmbedding f')
    (hy : range f = {y}ᶜ) (hy' : range f' = {y'}ᶜ) :
    Y ≃ₜ Y' :=
  (equivOfIsEmbeddingOfRangeEq y f hf hy).symm.trans
    (equivOfIsEmbeddingOfRangeEq y' f' hf' hy')

/-- Theorem 29.1 (2): The canonical homeomorphism between one-point extensions agrees with their
embeddings of `X`. -/
@[simp]
theorem compactificationEquiv_apply {X : Type u} [TopologicalSpace X]
    (Y : CompHaus.{v}) (Y' : CompHaus.{w}) (f : X → Y) (f' : X → Y') (y : Y) (y' : Y')
    (hf : IsEmbedding f) (hf' : IsEmbedding f')
    (hy : range f = {y}ᶜ) (hy' : range f' = {y'}ᶜ) (x : X) :
    compactificationEquiv Y Y' f f' y y' hf hf' hy hy' (f x) = f' x := by
  let e := equivOfIsEmbeddingOfRangeEq y f hf hy
  let e' := equivOfIsEmbeddingOfRangeEq y' f' hf' hy'
  have hfx : e.symm (f x) = x := by
    rw [← equivOfIsEmbeddingOfRangeEq_apply_coe y f hf hy x]
    exact e.symm_apply_apply x
  change e' (e.symm (f x)) = f' x
  rw [hfx]
  exact equivOfIsEmbeddingOfRangeEq_apply_coe y' f' hf' hy' x

/-- The canonical homeomorphism between one-point extensions maps the added point to the added
point. -/
@[simp]
theorem compactificationEquiv_extensionPoint {X : Type u} [TopologicalSpace X]
    (Y : CompHaus.{v}) (Y' : CompHaus.{w}) (f : X → Y) (f' : X → Y') (y : Y) (y' : Y')
    (hf : IsEmbedding f) (hf' : IsEmbedding f')
    (hy : range f = {y}ᶜ) (hy' : range f' = {y'}ᶜ) :
    compactificationEquiv Y Y' f f' y y' hf hf' hy hy' y = y' := by
  let e := equivOfIsEmbeddingOfRangeEq y f hf hy
  let e' := equivOfIsEmbeddingOfRangeEq y' f' hf' hy'
  have hy_eq : e.symm y = ∞ := by
    rw [← equivOfIsEmbeddingOfRangeEq_apply_infty y f hf hy]
    exact e.symm_apply_apply ∞
  change e' (e.symm y) = y'
  rw [hy_eq]
  exact equivOfIsEmbeddingOfRangeEq_apply_infty y' f' hf' hy'


end OnePoint
