module

import Topology_Munkres_2000.Book.Definition_69_7.Presentation

/- Definition 69.8 (1). A presentation of a group consists of an indexed generating
family and an indexed family of relators that normally generates the kernel of the
induced free-group homomorphism. -/
#check Group.Presentation

/- Definition 69.8 (2). A presentation with finitely many generators makes the
presented group finitely generated. -/
#check Group.Presentation.fg

/- Definition 69.8 (3). A presentation with finite generator and relator families
makes the presented group finitely presented. -/
#check Group.Presentation.isFinitelyPresented
