import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Construction_14_1_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.HurewiczComparison
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Theorem_14_3_1

open CategoryTheory
open HomotopicalAlgebra

noncomputable section

universe u

local notation "BasedSpace" => Under (⊤_ TopCat)
local notation "NBasedSpace" =>
  CategoryTheory.ObjectProperty.FullSubcategory
    (HomotopicalAlgebra.IsCofibrant : CategoryTheory.ObjectProperty BasedSpace)

-- Semantic recall via `lean_leansearch` only surfaced unrelated abstract homological shift APIs.
-- The repo's canonical sphere owner is `basedSphere`, while Theorem 14.3.1 is expressed relative
-- to an arbitrary `ReducedSuspensionModel`. This file therefore exposes a public bridge owner from
-- the suspension tower `Σ^n S^0` of a chosen model `S` to the canonical `basedSphere n`, together
-- with the `S^0`-to-`pointHomology` bridge needed for Corollary 14.3.3 and Chapter 15 reuse.

/-- A based-space isomorphism induces an isomorphism of the corresponding singleton-basepoint
pairs. -/
noncomputable def basedReducedPairIso {X Y : BasedSpace} (e : X ≅ Y) :
    basedReducedPair X ≅ basedReducedPair Y where
  hom := basedMapReducedPairHom e.hom
  inv := basedMapReducedPairHom e.inv
  hom_inv_id := by
    apply SpacePair.hom_ext
    change e.hom.right ≫ e.inv.right = 𝟙 X.right
    exact congrArg (fun f : X ⟶ X ↦ f.right) e.hom_inv_id
  inv_hom_id := by
    apply SpacePair.hom_ext
    change e.inv.right ≫ e.hom.right = 𝟙 Y.right
    exact congrArg (fun f : Y ⟶ Y ↦ f.right) e.inv_hom_id

/-- A based-space isomorphism induces an isomorphism on reduced homology. -/
noncomputable abbrev basedReducedHomologyIso
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (q : ℤ) {X Y : BasedSpace} (e : X ≅ Y) :
    (H.homology q).obj (basedReducedPair X) ≅
      (H.homology q).obj (basedReducedPair Y) :=
  (H.homology q).mapIso (basedReducedPairIso e)

/-- The suspension-generated sphere owner `Σ^n S^0` determined by a chosen reduced suspension
model `S` and a chosen `S^0`-model `sphereZero`. -/
def reducedHomologySuspensionSphere
    [CategoryWithCofibrations BasedSpace]
    (S : ReducedSuspensionModel) (sphereZero : NBasedSpace) : ℕ → NBasedSpace
  | 0 => sphereZero
  | n + 1 => S.suspension.obj (reducedHomologySuspensionSphere S sphereZero n)

/-- A bridge from the suspension tower `Σ^n S^0` of a chosen reduced suspension model `S` to the
canonical sphere owners `basedSphere n`. -/
private structure ReducedSuspensionSphereComparison
    [CategoryWithCofibrations BasedSpace]
    (S : ReducedSuspensionModel) where
  /-- The chosen nondegenerately based `S^0`-model at the bottom of the suspension tower. -/
  sphereZero : NBasedSpace
  /-- The degreewise identification of the suspension tower `Σ^n S^0` with the canonical sphere
  owner `basedSphere n`. -/
  sphereIso :
    ∀ n : ℕ, (reducedHomologySuspensionSphere S sphereZero n).obj ≅ basedSphere n

namespace ReducedSuspensionSphereComparison

/-- The chosen `S^0`-comparison at the bottom of the suspension tower. -/
private abbrev sphereZeroIso
    [CategoryWithCofibrations BasedSpace]
    {S : ReducedSuspensionModel} (comparison : ReducedSuspensionSphereComparison S) :
    comparison.sphereZero.obj ≅ basedSphere 0 :=
  comparison.sphereIso 0

/-- The `basedSphere n` reduced homology is identified with the reduced homology of the chosen
suspension-model sphere `Σ^n S^0`. -/
private noncomputable abbrev reducedHomologyIso
    [CategoryWithCofibrations BasedSpace]
    {S : ReducedSuspensionModel}
    (comparison : ReducedSuspensionSphereComparison S)
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (q : ℤ) (n : ℕ) :
    (H.homology q).obj (basedReducedPair (basedSphere n)) ≅
      (nBasedReducedHomologyFunctor H q).obj
        (reducedHomologySuspensionSphere S comparison.sphereZero n) :=
  basedReducedHomologyIso H q (comparison.sphereIso n).symm

/-- Unfolding `reducedHomologyIso` transports reduced homology across the chosen comparison
`basedSphere n ≅ Σ^n S^0`. -/
private theorem reducedHomologyIso_def
    [CategoryWithCofibrations BasedSpace]
    {S : ReducedSuspensionModel}
    (comparison : ReducedSuspensionSphereComparison S)
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (q : ℤ) (n : ℕ) :
    comparison.reducedHomologyIso H q n =
      basedReducedHomologyIso H q (comparison.sphereIso n).symm :=
  rfl

end ReducedSuspensionSphereComparison

/-- Iterating the chosen suspension isomorphism identifies the reduced homology of the
suspension-generated owner `Σ^n X` with the degree-shifted reduced homology of `X`. -/
noncomputable def reducedHomologyIteratedSuspensionShiftIso
    [CategoryWithCofibrations BasedSpace]
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (S : ReducedSuspensionModel)
    (η : ∀ r : ℤ,
      nBasedReducedHomologyFunctor H r ≅
        S.suspension ⋙ nBasedReducedHomologyFunctor H (r + 1))
    (X : NBasedSpace) :
    (r : ℤ) → (n : ℕ) →
      (nBasedReducedHomologyFunctor H (r + n)).obj
          (reducedHomologySuspensionSphere S X n) ≅
        (nBasedReducedHomologyFunctor H r).obj X
  | r, 0 =>
      (eqToIso (congrArg (nBasedReducedHomologyFunctor H) (Int.add_zero r))).app X
  | r, n + 1 =>
      (eqToIso
          (congrArg (nBasedReducedHomologyFunctor H) (Int.add_assoc r (n : ℤ) 1).symm)).app
          (S.suspension.obj (reducedHomologySuspensionSphere S X n)) ≪≫
        ((η (r + n)).app (reducedHomologySuspensionSphere S X n)).symm ≪≫
        reducedHomologyIteratedSuspensionShiftIso H S η X r n

/-- Relative to a chosen reduced suspension model `S` and a chosen `S^0`-model `sphereZero`,
iterating the suspension isomorphism of Theorem 14.3.1 identifies the reduced homology of the
suspension-generated sphere owner `reducedHomologySuspensionSphere S sphereZero n = Σ^n S^0`
with the degree-shifted reduced homology of `sphereZero`. -/
noncomputable abbrev reducedHomologySphereShiftToSphereZero
    [CategoryWithCofibrations BasedSpace]
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (S : ReducedSuspensionModel)
    (η : ∀ r : ℤ,
      nBasedReducedHomologyFunctor H r ≅
        S.suspension ⋙ nBasedReducedHomologyFunctor H (r + 1))
    (sphereZero : NBasedSpace)
    (q : ℤ) (n : ℕ) :
    (nBasedReducedHomologyFunctor H q).obj
        (reducedHomologySuspensionSphere S sphereZero n) ≅
      (nBasedReducedHomologyFunctor H (q - n)).obj sphereZero :=
  (eqToIso (congrArg (nBasedReducedHomologyFunctor H) (Int.sub_add_cancel q (n : ℤ)).symm)).app
      (reducedHomologySuspensionSphere S sphereZero n) ≪≫
    reducedHomologyIteratedSuspensionShiftIso H S η sphereZero (q - n) n

/-- Composing `reducedHomologySphereShiftToSphereZero` with a chosen comparison from the selected
`S^0`-model to point homology gives the corresponding shift isomorphism for the suspension model
`reducedHomologySuspensionSphere S sphereZero n = Σ^n S^0`. -/
noncomputable abbrev reducedHomologySuspensionSphereShiftToPoint
    [CategoryWithCofibrations BasedSpace]
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (S : ReducedSuspensionModel)
    (η : ∀ r : ℤ,
      nBasedReducedHomologyFunctor H r ≅
        S.suspension ⋙ nBasedReducedHomologyFunctor H (r + 1))
    (sphereZero : NBasedSpace)
    (q : ℤ) (n : ℕ)
    (sphereZeroToPoint :
      (nBasedReducedHomologyFunctor H (q - n)).obj sphereZero ≅
        ModuleCat.of ℤ (pointHomology H (q - n))) :
    (nBasedReducedHomologyFunctor H q).obj
        (reducedHomologySuspensionSphere S sphereZero n) ≅
      ModuleCat.of ℤ (pointHomology H (q - n)) :=
  reducedHomologySphereShiftToSphereZero H S η sphereZero q n ≪≫
    sphereZeroToPoint

/-- The reduced homology of the canonical `S^0 = basedSphere 0` is identified with point
homology. -/
theorem basedSphereZeroReducedHomologyToPoint
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (q : ℤ) :
    Nonempty
      ((H.homology q).obj (basedReducedPair (basedSphere 0)) ≅
        ModuleCat.of ℤ (pointHomology H q)) := sorry

/-- For a chosen reduced suspension model `S`, the repository's canonical sphere owner
`basedSphere n` is identified with the suspension tower `Σ^n S^0` for some chosen `S^0`-model.
-/
private theorem existsReducedSuspensionSphereComparison
    [CategoryWithCofibrations BasedSpace]
    (S : ReducedSuspensionModel) :
    Nonempty (ReducedSuspensionSphereComparison S) := sorry

namespace ReducedSuspensionSphereComparison

/-- Transporting the canonical `S^0`-to-point comparison along a chosen suspension-sphere
comparison identifies the reduced homology of the chosen `S^0`-model with point homology. -/
private theorem sphereZeroToPoint_nonempty
    [CategoryWithCofibrations BasedSpace]
    {S : ReducedSuspensionModel}
    (comparison : ReducedSuspensionSphereComparison S)
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (q : ℤ) :
    Nonempty
      ((nBasedReducedHomologyFunctor H q).obj comparison.sphereZero ≅
        ModuleCat.of ℤ (pointHomology H q)) := by
  let e₀ := comparison.reducedHomologyIso H q 0
  rcases basedSphereZeroReducedHomologyToPoint H q with ⟨e⟩
  exact ⟨e₀.symm ≪≫ e⟩

end ReducedSuspensionSphereComparison

/-- Given a public suspension-sphere comparison from the canonical sphere owner `basedSphere n`
to a chosen suspension model `Σ^n S^0`, and a comparison from the chosen `S^0`-model to
`pointHomology`, repeated suspension yields the resulting shift isomorphism
`ModuleCat.of ℤ (basedReducedHomology H q (basedSphere n)) ≅
  ModuleCat.of ℤ (pointHomology H (q - n))`. -/
private noncomputable abbrev reducedHomologySphereShiftViaComparison
    [CategoryWithCofibrations BasedSpace]
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (S : ReducedSuspensionModel)
    (η : ∀ r : ℤ,
      nBasedReducedHomologyFunctor H r ≅
        S.suspension ⋙ nBasedReducedHomologyFunctor H (r + 1))
    (comparison : ReducedSuspensionSphereComparison S)
    (q : ℤ) (n : ℕ)
    (sphereZeroToPoint :
      (nBasedReducedHomologyFunctor H (q - n)).obj comparison.sphereZero ≅
        ModuleCat.of ℤ (pointHomology H (q - n))) :
    (H.homology q).obj (basedReducedPair (basedSphere n)) ≅
      ModuleCat.of ℤ (pointHomology H (q - n)) :=
  comparison.reducedHomologyIso H q n ≪≫
    reducedHomologySuspensionSphereShiftToPoint H S η comparison.sphereZero q n
      sphereZeroToPoint

/-- Unfolding `reducedHomologySphereShiftViaComparison` first transports reduced homology along
`basedSphere n ≅ Σ^n S^0`, then applies the iterated suspension shift and the chosen
`S^0`-to-point comparison. -/
private theorem reducedHomologySphereShiftViaComparison_def
    [CategoryWithCofibrations BasedSpace]
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (S : ReducedSuspensionModel)
    (η : ∀ r : ℤ,
      nBasedReducedHomologyFunctor H r ≅
        S.suspension ⋙ nBasedReducedHomologyFunctor H (r + 1))
    (comparison : ReducedSuspensionSphereComparison S)
    (q : ℤ) (n : ℕ)
    (sphereZeroToPoint :
      (nBasedReducedHomologyFunctor H (q - n)).obj comparison.sphereZero ≅
        ModuleCat.of ℤ (pointHomology H (q - n))) :
    reducedHomologySphereShiftViaComparison H S η comparison q n sphereZeroToPoint =
      comparison.reducedHomologyIso H q n ≪≫
        reducedHomologySuspensionSphereShiftToPoint H S η comparison.sphereZero q n
          sphereZeroToPoint :=
  rfl

namespace ReducedSuspensionSphereComparison

/-- A chosen suspension-sphere comparison and the canonical `S^0`-to-point comparison together
package the sphere-shift isomorphism on the reduced-pair homology owner used by the explicit
comparison API. -/
private theorem reducedHomologySphereShift_nonempty
    [CategoryWithCofibrations BasedSpace]
    {S : ReducedSuspensionModel}
    (comparison : ReducedSuspensionSphereComparison S)
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (η : ∀ r : ℤ,
      nBasedReducedHomologyFunctor H r ≅
        S.suspension ⋙ nBasedReducedHomologyFunctor H (r + 1))
    (q : ℤ) (n : ℕ) :
    Nonempty
      ((H.homology q).obj (basedReducedPair (basedSphere n)) ≅
        ModuleCat.of ℤ (pointHomology H (q - n))) := by
  rcases comparison.sphereZeroToPoint_nonempty H (q - n) with ⟨sphereZeroToPoint⟩
  exact ⟨reducedHomologySphereShiftViaComparison H S η comparison q n sphereZeroToPoint⟩

end ReducedSuspensionSphereComparison

/-- Corollary 14.3.3. For any `n` and `q`, repeated suspension gives an isomorphism
`ModuleCat.of ℤ (basedReducedHomology H q (basedSphere n)) ≅
  ModuleCat.of ℤ (pointHomology H (q - n))`. -/
theorem reducedHomologySphereShift
    [CategoryWithCofibrations BasedSpace]
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (q : ℤ) (n : ℕ) :
    Nonempty
      (ModuleCat.of ℤ (basedReducedHomology H q (basedSphere n)) ≅
        ModuleCat.of ℤ (pointHomology H (q - n))) := sorry

/-- Unfolding `reducedHomologySphereShiftToSphereZero` gives the iterated suspension-shift
isomorphism
from `Ẽ_q(Σ^n S^0)` to `Ẽ_(q - n)(S^0)` for the chosen `S^0`-model `sphereZero`. -/
theorem reducedHomologySphereShiftToSphereZero_def
    [CategoryWithCofibrations BasedSpace]
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (S : ReducedSuspensionModel)
    (η : ∀ r : ℤ,
      nBasedReducedHomologyFunctor H r ≅
        S.suspension ⋙ nBasedReducedHomologyFunctor H (r + 1))
    (sphereZero : NBasedSpace)
    (q : ℤ) (n : ℕ) :
    reducedHomologySphereShiftToSphereZero H S η sphereZero q n =
      (eqToIso
          (congrArg (nBasedReducedHomologyFunctor H) (Int.sub_add_cancel q (n : ℤ)).symm)).app
          (reducedHomologySuspensionSphere S sphereZero n) ≪≫
        reducedHomologyIteratedSuspensionShiftIso H S η sphereZero (q - n) n := rfl
