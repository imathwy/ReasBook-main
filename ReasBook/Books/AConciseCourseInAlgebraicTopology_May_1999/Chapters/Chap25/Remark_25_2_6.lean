import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Construction_25_2_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Theorem_25_2_3

/- Remark 25.2.6. Pontryagin-Thom theory translates the geometric cobordism problem into homotopy-
theoretic data: Construction 25.2.2 provides the Pontryagin-Thom collapse map from an embedded
closed manifold into the Thom space `TO q`, and Theorem 25.2.3 identifies unoriented cobordism
groups first with sufficiently far-out homotopy groups of the Thom spaces `TO q` and then with
the corresponding stable homotopy groups of the Thom-space prespectrum. Accordingly, this source
remark is formalized as a labeled recall block pointing to those existing Chapter 25 owners rather
than as a new wrapper theorem. -/
#check PontryaginThomConstruction
#check PontryaginThomConstruction.normalBundle
#check PontryaginThomConstruction.classifiesNormalBundle
#check PontryaginThomConstruction.collapseMap
#check unorientedCobordismGroup_eventually_mulEquiv_homotopyGroup_TO
#check unorientedCobordismGroup_mulEquiv_stableHomotopyGroup_TO
