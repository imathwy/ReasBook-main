import Mathlib.Algebra.Group.TypeTags.Hom
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Definition_13_2_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.HurewiczComparison
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Definition_24_6_1

open CategoryTheory
open scoped TopCat Topology Topology.Homotopy

noncomputable section

-- Chapter 14 already exposes the canonical sphere owner `basedSphere` and the corresponding
-- `HurewiczComparison` owner. This file keeps the source-facing Hopf-invariant class-function
-- surface on `basedHomotopyClasses (basedSphere (2 * m + 1)) (basedSphere (m + 1))`. For the
-- degree hypotheses in Proposition 24.6.2 (1) and (2), the file now bridges directly to the
-- Chapter 13 owner `SphereSelfMap.HasDegree` by transporting `basedSphere` self-maps across an
-- explicit comparison `suspensionSphere (m + 1) ≅ basedSphere (m + 1)`.

/-- Transport a based self-map of `basedSphere (m + 1)` to the Chapter 13 continuous self-map
owner on `suspensionSphere (m + 1)` along an explicit comparison of sphere models. -/
abbrev basedSphereSelfMapOnSuspensionSphere
    (m : ℕ)
    (sphereIso : (suspensionSphere (m + 1)).toBasedSpace ≅ basedSphere (m + 1))
    (f : basedSphere (m + 1) ⟶ basedSphere (m + 1)) :
    SphereSelfMap m.succPNat :=
  let h :
      (suspensionSphere (m + 1)).toCompactlyGenerated ≃ₜ (basedSphere (m + 1)).right :=
    TopCat.homeoOfIso ((Under.forget (⊤_ TopCat)).mapIso sphereIso)
  let hMap :
      C((suspensionSphere (m + 1)).toCompactlyGenerated, (basedSphere (m + 1)).right) :=
    ⟨h, h.continuous_toFun⟩
  let hInv :
      C((basedSphere (m + 1)).right, (suspensionSphere (m + 1)).toCompactlyGenerated) :=
    ⟨h.symm, h.continuous_invFun⟩
  let fMap :
      C((basedSphere (m + 1)).right, (basedSphere (m + 1)).right) :=
    f.right.hom
  hInv.comp (fMap.comp hMap)

/-- The underlying continuous map of a based representative `S^(2m + 1) ⟶ S^(m + 1)`, viewed as
the Chapter 24 owner `HopfSphereMap (m + 1)`. -/
abbrev basedSphereRepresentativeMap
    (m : ℕ) (f : basedSphere (2 * m + 1) ⟶ basedSphere (m + 1)) :
    HopfSphereMap (m + 1) :=
  f.right.hom

/-- The based homotopy class represented by `f : basedSphere (2 * m + 1) ⟶ basedSphere (m + 1)`. -/
abbrev basedSphereRepresentativeClass
    (m : ℕ) (f : basedSphere (2 * m + 1) ⟶ basedSphere (m + 1)) :
    basedHomotopyClasses (basedSphere (2 * m + 1)) (basedSphere (m + 1)) :=
  Quotient.mk (basedHomotopySetoid (basedSphere (2 * m + 1)) (basedSphere (m + 1))) f

/-- Precomposing a based representative with a based self-map of the source sphere, viewed on the
Chapter 24 `HopfSphereMap` owner. -/
abbrev hopfRepresentativePrecompose
    (m : ℕ)
    (f : basedSphere (2 * m + 1) ⟶ basedSphere (m + 1))
    (u : basedSphere (2 * m + 1) ⟶ basedSphere (2 * m + 1)) :
    HopfSphereMap (m + 1) :=
  basedSphereRepresentativeMap m (u ≫ f)

/-- Postcomposing a based representative with a based self-map of the target sphere, viewed on the
Chapter 24 `HopfSphereMap` owner. -/
abbrev hopfRepresentativePostcompose
    (m : ℕ)
    (f : basedSphere (2 * m + 1) ⟶ basedSphere (m + 1))
    (v : basedSphere (m + 1) ⟶ basedSphere (m + 1)) :
    HopfSphereMap (m + 1) :=
  basedSphereRepresentativeMap m (f ≫ v)

/-- Proposition 24.6.2 (1): writing the source positivity hypothesis as `n = m + 1`,
precomposing `f : S^(2m + 1) → S^(m + 1)` with a degree-`d` self-map of the source sphere
multiplies its Hopf invariant by `d`, where the degree is read through a supplied comparison
`suspensionSphere (2m + 1) ≅ basedSphere (2m + 1)` and the Chapter 13 owner
`SphereSelfMap.HasDegree`. -/
theorem hopfInvariant_precompose_degree
    {m : ℕ} {f : basedSphere (2 * m + 1) ⟶ basedSphere (m + 1)} {h d : ℤ}
    (hf : IsHopfInvariant (basedSphereRepresentativeMap m f) h)
    {u : basedSphere (2 * m + 1) ⟶ basedSphere (2 * m + 1)}
    (sourceIso : (suspensionSphere (2 * m + 1)).toBasedSpace ≅ basedSphere (2 * m + 1))
    (hu :
      SphereSelfMap.HasDegree (2 * m).succPNat
        (basedSphereSelfMapOnSuspensionSphere (2 * m) sourceIso u) d) :
    IsHopfInvariant (hopfRepresentativePrecompose m f u) (d * h) := sorry

/-- Proposition 24.6.2 (2): writing the source positivity hypothesis as `n = m + 1`,
postcomposing `f : S^(2m + 1) → S^(m + 1)` with a degree-`d` self-map of the target sphere
multiplies its Hopf invariant by `d^2`, where the degree is read through a supplied comparison
`suspensionSphere (m + 1) ≅ basedSphere (m + 1)` and the Chapter 13 owner
`SphereSelfMap.HasDegree`. -/
theorem hopfInvariant_postcompose_degree
    {m : ℕ} {f : basedSphere (2 * m + 1) ⟶ basedSphere (m + 1)} {h d : ℤ}
    (hf : IsHopfInvariant (basedSphereRepresentativeMap m f) h)
    {v : basedSphere (m + 1) ⟶ basedSphere (m + 1)}
    (targetIso : (suspensionSphere (m + 1)).toBasedSpace ≅ basedSphere (m + 1))
    (hv :
      SphereSelfMap.HasDegree m.succPNat
        (basedSphereSelfMapOnSuspensionSphere m targetIso v) d) :
    IsHopfInvariant (hopfRepresentativePostcompose m f v) (d ^ 2 * h) := sorry

/-- A function on based homotopy classes of maps `S^(2m + 1) ⟶ S^(m + 1)` is the Hopf-invariant
class function when its value on each class represented by `f` is a Hopf invariant of `f`. -/
def IsHopfInvariantOnSphereClasses
    (m : ℕ)
    (ψ : basedHomotopyClasses (basedSphere (2 * m + 1)) (basedSphere (m + 1)) → ℤ) : Prop :=
  ∀ f : basedSphere (2 * m + 1) ⟶ basedSphere (m + 1),
    IsHopfInvariant (basedSphereRepresentativeMap m f) (ψ (basedSphereRepresentativeClass m f))

/-- Evaluating a Hopf-invariant class function on the class of a based representative produces a
Hopf invariant of that representative. -/
theorem IsHopfInvariantOnSphereClasses.isHopfInvariant
    {m : ℕ}
    {ψ : basedHomotopyClasses (basedSphere (2 * m + 1)) (basedSphere (m + 1)) → ℤ}
    (hψ : IsHopfInvariantOnSphereClasses m ψ)
    (f : basedSphere (2 * m + 1) ⟶ basedSphere (m + 1)) :
    IsHopfInvariant (basedSphereRepresentativeMap m f) (ψ (basedSphereRepresentativeClass m f)) :=
  sorry

/-- A total Hopf-invariant class function exists on based homotopy classes of sphere maps. -/
theorem exists_hopfInvariantOnSphereClasses
    (m : ℕ) :
    ∃ ψ : basedHomotopyClasses (basedSphere (2 * m + 1)) (basedSphere (m + 1)) → ℤ,
      IsHopfInvariantOnSphereClasses m ψ := sorry

/-- Transporting a Hopf-invariant class function along a fixed comparison equivalence yields an
additive homomorphism on the canonical homotopy-group owner. -/
noncomputable def hopfInvariantHomomorphismViaComparison
    (m : ℕ)
    (comparison : HurewiczComparison (2 * m + 1) (basedSphere (m + 1)))
    (ψ : basedHomotopyClasses (basedSphere (2 * m + 1)) (basedSphere (m + 1)) → ℤ) :
    Additive (π_ (2 * m + 1) (𝕊 (m + 1)) (underTopBasepoint (basedSphere (m + 1)))) →+ ℤ where
  toFun := fun a ↦ ψ (comparison.toSphereClass a.toMul)
  map_zero' := sorry
  map_add' := sorry

/-- The transported Hopf-invariant homomorphism has underlying function
`a ↦ ψ (comparison.toSphereClass a.toMul)`. -/
theorem hopfInvariantHomomorphismViaComparison_apply
    (m : ℕ)
    (comparison : HurewiczComparison (2 * m + 1) (basedSphere (m + 1)))
    (ψ : basedHomotopyClasses (basedSphere (2 * m + 1)) (basedSphere (m + 1)) → ℤ)
    (a : Additive (π_ (2 * m + 1) (𝕊 (m + 1)) (underTopBasepoint (basedSphere (m + 1))))) :
    hopfInvariantHomomorphismViaComparison m comparison ψ a =
      ψ (comparison.toSphereClass a.toMul) :=
  rfl

/-- Via a supplied Chapter 14.3.3 comparison, the transported Hopf-invariant homomorphism sends
the class of a based representative `f` to a Hopf invariant of `f`. -/
theorem hopfInvariantHomomorphismViaComparison_spec
    {m : ℕ}
    (comparison : HurewiczComparison (2 * m + 1) (basedSphere (m + 1)))
    {ψ : basedHomotopyClasses (basedSphere (2 * m + 1)) (basedSphere (m + 1)) → ℤ}
    (hψ : IsHopfInvariantOnSphereClasses m ψ)
    (f : basedSphere (2 * m + 1) ⟶ basedSphere (m + 1)) :
    IsHopfInvariant (basedSphereRepresentativeMap m f)
      (hopfInvariantHomomorphismViaComparison m comparison ψ
        (Additive.ofMul
          (comparison.ofSphereClass (basedSphereRepresentativeClass m f)))) :=
  sorry

/-- Relative to the named Chapter 14.3.3 comparison on `basedSphere (m + 1)`, the Hopf invariant
induces the canonical additive homomorphism on `π_ (2 * m + 1)(𝕊 (m + 1))`. -/
noncomputable def hopfInvariantHomomorphism
    (m : ℕ) [HasHurewiczComparison (2 * m + 1) (basedSphere (m + 1))]
    (ψ : basedHomotopyClasses (basedSphere (2 * m + 1)) (basedSphere (m + 1)) → ℤ) :
    Additive (π_ (2 * m + 1) (𝕊 (m + 1)) (underTopBasepoint (basedSphere (m + 1)))) →+ ℤ :=
  hopfInvariantHomomorphismViaComparison m
    (hurewiczComparison (2 * m + 1) (basedSphere (m + 1))) ψ

/-- The canonical Hopf-invariant homomorphism has underlying function
`a ↦ ψ ((hurewiczComparison _ _).toSphereClass a.toMul)`. -/
theorem hopfInvariantHomomorphism_apply
    (m : ℕ) [HasHurewiczComparison (2 * m + 1) (basedSphere (m + 1))]
    (ψ : basedHomotopyClasses (basedSphere (2 * m + 1)) (basedSphere (m + 1)) → ℤ)
    (a : Additive (π_ (2 * m + 1) (𝕊 (m + 1)) (underTopBasepoint (basedSphere (m + 1))))) :
    hopfInvariantHomomorphism m ψ a =
      ψ ((hurewiczComparison (2 * m + 1) (basedSphere (m + 1))).toSphereClass a.toMul) :=
  rfl

/-- The canonical Hopf-invariant homomorphism sends the `π_ (2 * m + 1)`-class of a based
representative `f` to a Hopf invariant of `f`. -/
theorem hopfInvariantHomomorphism_spec
    {m : ℕ} [HasHurewiczComparison (2 * m + 1) (basedSphere (m + 1))]
    {ψ : basedHomotopyClasses (basedSphere (2 * m + 1)) (basedSphere (m + 1)) → ℤ}
    (hψ : IsHopfInvariantOnSphereClasses m ψ)
    (f : basedSphere (2 * m + 1) ⟶ basedSphere (m + 1)) :
    IsHopfInvariant (basedSphereRepresentativeMap m f)
      (hopfInvariantHomomorphism m ψ
        (Additive.ofMul
          ((hurewiczComparison (2 * m + 1) (basedSphere (m + 1))).ofSphereClass
            (basedSphereRepresentativeClass m f)))) := by
  simpa [hopfInvariantHomomorphism] using
    hopfInvariantHomomorphismViaComparison_spec
      (hurewiczComparison (2 * m + 1) (basedSphere (m + 1))) hψ f

/-- Proposition 24.6.2 (3): writing the source positivity hypothesis as `n = m + 1`,
for any fixed Chapter 14.3.3 comparison between
`π_ (2 * m + 1) (𝕊 (m + 1)) (underTopBasepoint (basedSphere (m + 1)))` and the based homotopy
classes of maps
`S^(2m + 1) ⟶ S^(m + 1)`, the Hopf invariant induces an additive homomorphism to `ℤ` whose value
on the class of each representative `f` is a Hopf invariant of `f`. -/
theorem hopfInvariantHomomorphism_exists
    (m : ℕ)
    (comparison : HurewiczComparison (2 * m + 1) (basedSphere (m + 1))) :
    ∃ ψ :
      Additive
        (π_ (2 * m + 1) (𝕊 (m + 1)) (underTopBasepoint (basedSphere (m + 1)))) →+ ℤ,
      ∀ f : basedSphere (2 * m + 1) ⟶ basedSphere (m + 1),
        IsHopfInvariant (basedSphereRepresentativeMap m f)
          (ψ
            (Additive.ofMul
              (comparison.ofSphereClass (basedSphereRepresentativeClass m f)))) :=
  sorry

/-- With a named Chapter 14.3.3 comparison on `basedSphere (m + 1)`, Proposition 24.6.2 (3)
specializes to the canonical owner `hopfInvariantHomomorphism`. -/
theorem hopfInvariantHomomorphism_exists_of_hasHurewiczComparison
    (m : ℕ) [HasHurewiczComparison (2 * m + 1) (basedSphere (m + 1))] :
    ∃ ψ :
      Additive
        (π_ (2 * m + 1) (𝕊 (m + 1)) (underTopBasepoint (basedSphere (m + 1)))) →+ ℤ,
      ∀ f : basedSphere (2 * m + 1) ⟶ basedSphere (m + 1),
        IsHopfInvariant (basedSphereRepresentativeMap m f)
          (ψ
            (Additive.ofMul
              ((hurewiczComparison (2 * m + 1) (basedSphere (m + 1))).ofSphereClass
                (basedSphereRepresentativeClass m f)))) := by
  simpa [hopfInvariantHomomorphism] using
    hopfInvariantHomomorphism_exists m
      (hurewiczComparison (2 * m + 1) (basedSphere (m + 1)))
