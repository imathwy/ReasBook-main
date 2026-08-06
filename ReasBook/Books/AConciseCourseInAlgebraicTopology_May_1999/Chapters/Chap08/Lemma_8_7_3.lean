import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Definition_6_5_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_4_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Pullback_8_6_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Construction_8_7_2

open CategoryTheory

noncomputable section

local notation "BasedSpace" => Under (⊤_ TopCat)

/- Lemma 8.7.3 has two comparison squares. The loop-side square is exported by
`Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Construction_8_7_2` and rechecked in
`Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Remark_8_7_5`; this file keeps the suspension-side square. -/

section

variable {X Y : BasedSpace} (f : X ⟶ Y)

/-- Lemma 8.7.3 (2). The comparison map `ε : ΣF_f ⟶ C_f` from Construction 8.7.2 makes the
outgoing square from the suspended fiber sequence to the cofiber sequence homotopy commute:
composing `ε` with `C_f ⟶ ΣX` is homotopic under the basepoint to the signed suspension of the
projection `π(f) : F_f ⟶ X`. -/
theorem homotopyFiberSuspensionToHomotopyCofiber_comp_cofiberStructureMap_homotopic
    :
    HomotopicUnder
      (homotopyFiberSuspensionToHomotopyCofiber f ≫ cofiberStructureMap f)
      (signedBasedSuspensionMap (homotopyFiberProjection f)) :=
  sorry

end
