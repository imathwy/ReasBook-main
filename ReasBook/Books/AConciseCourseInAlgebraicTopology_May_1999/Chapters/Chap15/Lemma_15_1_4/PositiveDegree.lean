import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap15.Lemma_15_1_3

open scoped TopCat Topology Topology.Homotopy

noncomputable section

universe u

local notation "BasedSpace" => CategoryTheory.Under (⊤_ TopCat)

/-- The canonical witness that `Fin n` is nonempty in positive degree. -/
theorem positiveDegreeFinNonempty (n : ℕ) (h_n : 1 < n) : Nonempty (Fin n) :=
  Fin.pos_iff_nonempty.1 (Nat.lt_trans Nat.zero_lt_one h_n)

instance (n : ℕ) [Fact (1 < n)] : Nonempty (Fin n) :=
  positiveDegreeFinNonempty n Fact.out

/-- The additive form of `π_ n(X)` used by the Chapter 15 positive-degree bridges. Its carrier
does not depend on the proof that `1 < n`; only the additive-group structure does. -/
abbrev positiveDegreeAdditiveHomotopyGroup
    (n : ℕ) (h_n : 1 < n) (X : BasedSpace) : Type u :=
  letI : Fact (1 < n) := ⟨h_n⟩
  Additive (π_ n X.right (underTopBasepoint X))

/-- The positive-degree additive homotopy group carries its canonical additive-group structure. -/
noncomputable instance positiveDegreeAdditiveHomotopyGroup.instAddGroup
    (n : ℕ) (h_n : 1 < n) (X : BasedSpace) :
    AddGroup (positiveDegreeAdditiveHomotopyGroup n h_n X) :=
  letI : Fact (1 < n) := ⟨h_n⟩
  Additive.addGroup

section

variable {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)

/-- The positive-degree Hurewicz homomorphism on `X`, with the positive-degree hypothesis exposed
as the ordinary binder `h_n : 1 < n` and the resulting `[Nonempty (Fin n)]` witness kept
internal. -/
noncomputable abbrev positiveDegreeHurewiczHomomorphismAtBasedSpace
    (n : ℕ) (h_n : 1 < n) (X : BasedSpace)
    [HasHurewiczComparison n X] (i_n : SphereHomologyGenerator H n) :
    positiveDegreeAdditiveHomotopyGroup n h_n X →+
      basedReducedHomology H (n : ℤ) X :=
  letI : Fact (1 < n) := ⟨h_n⟩
  hurewiczHomomorphism H n X i_n

/-- The positive-degree map on homotopy groups induced by a based map. -/
noncomputable abbrev positiveDegreeBasedHomotopyGroupHom
    (n : ℕ) (h_n : 1 < n) {X Y : BasedSpace} (f : X ⟶ Y) :
    positiveDegreeAdditiveHomotopyGroup n h_n X →+
      positiveDegreeAdditiveHomotopyGroup n h_n Y :=
  letI : Fact (1 < n) := ⟨h_n⟩
  basedHomotopyGroupHom n f

end
