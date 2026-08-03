module

public import Topology_Munkres_2000.Book.Corollary_59_2
public import Topology_Munkres_2000.Book.Definition_55_2.Sphere
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Geometry.Manifold.Instances.Sphere

public section

open scoped EuclideanSpace

namespace StandardSphere

/-- Helper for Theorem 59.3: stereographic projection identifies a punctured standard sphere
with Euclidean space of the same dimension. -/
private noncomputable def puncturedHomeomorphEuclidean (n : ℕ) (p : StandardSphere n) :
    ({p}ᶜ : Set (StandardSphere n)) ≃ₜ EuclideanSpace ℝ (Fin n) :=
  -- Restrict the partial chart to its source and identify its full target with Euclidean space.
  ((Homeomorph.setCongr (stereographic'_source (n := n) p).symm).trans
    (stereographic' n p).toHomeomorphSourceTarget).trans
      ((Homeomorph.setCongr (stereographic'_target (n := n) p)).trans
        (Homeomorph.Set.univ _))

/-- Helper for Theorem 59.3: the complement of one point in a standard sphere is simply
connected. -/
private lemma isSimplyConnected_compl_singleton (n : ℕ) (p : StandardSphere n) :
    IsSimplyConnected ({p}ᶜ : Set (StandardSphere n)) := by
  -- Transfer Euclidean simple connectedness across the stereographic homeomorphism.
  exact (puncturedHomeomorphEuclidean n p).toHomotopyEquiv.simplyConnectedSpace

/-- Helper for Theorem 59.3: deleting two distinct points from a standard sphere of dimension
at least two leaves a path-connected set. -/
private lemma isPathConnected_compl_pair (n : ℕ) (hn : 2 ≤ n) (p q : StandardSphere n)
    (hpq : p ≠ q) : IsPathConnected ({p}ᶜ ∩ {q}ᶜ) := by
  let e := puncturedHomeomorphEuclidean n p
  have hq : q ∈ ({p}ᶜ : Set (StandardSphere n)) := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hpq.symm
  let q' : ({p}ᶜ : Set (StandardSphere n)) := ⟨q, hq⟩
  have hn' : 1 < n := by
    omega
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin n)) := by
    apply Module.one_lt_rank_of_one_lt_finrank
    simpa only [finrank_euclideanSpace_fin] using hn'
  have hEuclidean : IsPathConnected ({e q'}ᶜ : Set (EuclideanSpace ℝ (Fin n))) :=
    isPathConnected_compl_singleton_of_one_lt_rank hrank (e q')
  -- Pull the Euclidean singleton complement back through the chart.
  have hpreimage : IsPathConnected (e ⁻¹' ({e q'}ᶜ : Set (EuclideanSpace ℝ (Fin n)))) :=
    e.isPathConnected_preimage.mpr hEuclidean
  have hq'_coe : (q' : StandardSphere n) = q := by
    simp only [q']
  have hpreimage_eq :
      e ⁻¹' ({e q'}ᶜ : Set (EuclideanSpace ℝ (Fin n))) =
        Subtype.val ⁻¹' ({q}ᶜ : Set (StandardSphere n)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff,
      e.injective.eq_iff, Subtype.ext_iff, hq'_coe]
  rw [hpreimage_eq] at hpreimage
  -- Map the subtype set back to the sphere; its image is exactly the pair complement.
  have himage :=
    Topology.IsInducing.subtypeVal.isPathConnected_iff.mp hpreimage
  simpa only [Subtype.image_preimage_val] using himage

end StandardSphere

/-- Theorem 59.3: If `n ≥ 2`, the `n`-sphere `Sⁿ` is simply connected. -/
theorem simplyConnectedSpace_standardSphere (n : ℕ) (hn : 2 ≤ n) :
    SimplyConnectedSpace (StandardSphere n) := by
  obtain ⟨p⟩ : Nonempty (StandardSphere n) :=
    NormedSpace.sphere_nonempty_rclike ℝ zero_le_one
  have hpneg : p ≠ -p := ne_neg_of_mem_unit_sphere ℝ p
  -- Cover the sphere by the two stereographic domains centered at antipodal points.
  apply SimplyConnectedSpace.of_isOpen_cover ({p}ᶜ) ({-p}ᶜ)
  · exact isOpen_compl_singleton
  · exact isOpen_compl_singleton
  · ext x
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_univ,
      iff_true]
    by_contra h
    push Not at h
    exact hpneg (h.1.symm.trans h.2)
  · exact StandardSphere.isPathConnected_compl_pair n hn p (-p) hpneg
  · exact StandardSphere.isSimplyConnected_compl_singleton n p
  · exact StandardSphere.isSimplyConnected_compl_singleton n (-p)
