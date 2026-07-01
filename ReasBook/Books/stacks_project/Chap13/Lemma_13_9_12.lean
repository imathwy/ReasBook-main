import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits ComplexShape HomologicalComplex
open CategoryTheory.Pretriangulated

universe v u

section

variable {V : Type u} [Category.{v} V] [Preadditive V] [HasZeroObject V] [HasBinaryBiproducts V]

local notation "Q" => HomotopyCategory.quotient V (up ℤ)

/- Domain-style sampling:
- primary domain: degreewise split short complexes of cochain complexes, their canonical
  distinguished triangles in the homotopy category, and the exact Hom-sequence segment that forces
  a middle composite to vanish;
- sampled owner declarations:
  `CochainComplex.trianglehOfDegreewiseSplit`,
  `HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit`,
  `Triangle.coyoneda_exact₂`,
  `Triangle.yoneda_exact₂`;
- best owner abstraction: the distinguished triangle
  `CochainComplex.trianglehOfDegreewiseSplit S₂ σ₂` attached to a chosen degreewise splitting of
  the middle termwise split exact sequence; the public source-facing owner data are only `S₂`
  together with the existence property `∀ n : ℤ, Nonempty ((S₂.map (eval V (up ℤ) n)).Splitting)`,
  as established in `Definition_13_9_9`;
- primitive data: the middle short complex `S₂`, its degreewise split existence property,
  arbitrary source and target cochain complexes for the maps into and out of `S₂.X₂`, and the two
  vanishing
  composites
  `(HomotopyCategory.quotient V (up ℤ)).map b ≫ (HomotopyCategory.quotient V (up ℤ)).map S₂.g = 0`
  and
  `(HomotopyCategory.quotient V (up ℤ)).map S₂.f ≫ (HomotopyCategory.quotient V (up ℤ)).map b' = 0`;
- derived API: any ambient outer split short complexes from the textbook diagram are unnecessary
  for this exactness argument once the middle row is expressed through its owner triangle. A chosen
  splitting family `σ₂` is bridge-level proof data, not part of the public vanishing statement.

Source/core/bridge triage:
- `source-facing`: the Stacks-project vanishing statement for the composite of the two middle maps;
- `core/canonical`: the middle distinguished triangle and the exactness owners
  `Triangle.coyoneda_exact₂` and `Triangle.yoneda_exact₂`;
- `bridge/view`: the passage from a termwise split short complex to its distinguished triangle via
  `trianglehOfDegreewiseSplit`.
-/

-- Proof sketch: view the middle termwise split short complex `S₂` through its canonical
-- distinguished triangle in the homotopy category. Exactness of `Hom(Q.obj X, -)` at the middle
-- term factors `Q.map b` through `Q.map S₂.f`, while exactness of `Hom(-, Q.obj Y)` factors
-- `Q.map b'` through `Q.map S₂.g`.
-- Their composite is therefore a multiple of
-- `Q.map S₂.f ≫ Q.map S₂.g = 0`.
/-- Lemma 13.9.12: let `S₂` be a termwise split exact sequence of cochain complexes in an additive
category, encoded as a short complex with a splitting after evaluation in every degree. If
`b : X ⟶ S₂.X₂` and `b' : S₂.X₂ ⟶ Y` become composable maps in the homotopy category `K(V)` with
`Q(b) ≫ Q(S₂.g) = 0` and `Q(S₂.f) ≫ Q(b') = 0`, then `Q(b) ≫ Q(b') = 0`. -/
theorem comp_eq_zero_in_homotopyCategory_of_termwiseSplit
    {S₂ : ShortComplex (CochainComplex V ℤ)}
    (hσ₂ : ∀ n : ℤ, Nonempty ((S₂.map (eval V (up ℤ) n)).Splitting))
    {X Y : CochainComplex V ℤ}
    {b : X ⟶ S₂.X₂} {b' : S₂.X₂ ⟶ Y}
    (hb_right : (Q).map b ≫ (Q).map S₂.g = 0)
    (hb'_left : (Q).map S₂.f ≫ (Q).map b' = 0) :
    (Q).map b ≫ (Q).map b' = 0 := by
  classical
  let σ₂ : ∀ n : ℤ, (S₂.map (eval V (up ℤ) n)).Splitting := fun n ↦ Classical.choice (hσ₂ n)
  let T := CochainComplex.trianglehOfDegreewiseSplit S₂ σ₂
  have hT : T ∈ distTriang (HomotopyCategory V (up ℤ)) :=
    (HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit T).2
      ⟨S₂, σ₂, ⟨Iso.refl _⟩⟩
  obtain ⟨a, ha⟩ := T.coyoneda_exact₂ hT ((Q).map b) (by simpa [T] using hb_right)
  obtain ⟨c, hc⟩ := T.yoneda_exact₂ hT ((Q).map b') (by simpa [T] using hb'_left)
  calc
    (Q).map b ≫ (Q).map b' = (a ≫ T.mor₁) ≫ (Q).map b' := by
      exact congrArg (fun f ↦ f ≫ (Q).map b') ha
    _ = (a ≫ T.mor₁) ≫ (T.mor₂ ≫ c) := by
      exact congrArg (fun f ↦ (a ≫ T.mor₁) ≫ f) hc
    _ = a ≫ (T.mor₁ ≫ T.mor₂) ≫ c := by simp [Category.assoc]
    _ = 0 := by rw [comp_distTriang_mor_zero₁₂ _ hT, zero_comp, comp_zero]

end
