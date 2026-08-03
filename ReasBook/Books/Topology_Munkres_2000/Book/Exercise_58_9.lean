module

public import Topology_Munkres_2000.Book.Exercise_58_9.Degree

public section

/- Exercise 58.9 (1). -/
#check Circle.FundamentalOrientation

/- Exercise 58.9 (2). -/
#check Circle.nonemptyFundamentalOrientation

/- Exercise 58.9 (3). -/
#check Circle.FundamentalOrientation.equiv

/- Exercise 58.9 (4). -/
#check Circle.FundamentalOrientation.map_path

/- Exercise 58.9 (5). -/
#check CircleMap.degreeAt

/- Exercise 58.9 (6). -/
#check CircleMap.degree

/- Exercise 58.9 (7). -/
#check CircleMap.degreeAt_eq_degree

/- Exercise 58.9 (8). -/
#check CircleMap.degree_eq

/- Exercise 58.9 (9). -/
#check CircleMap.degree_eq_of_homotopic

/- Exercise 58.9 (10). -/
#check CircleMap.degree_comp

/- Exercise 58.9 (11). -/
#check CircleMap.degree_const

/- Exercise 58.9 (12). -/
#check CircleMap.degree_id

/- Exercise 58.9 (13). -/
#check CircleMap.reflection

/- Exercise 58.9 (14). -/
#check CircleMap.degree_reflection

/- Exercise 58.9 (15). -/
#check CircleMap.zpower

/- Exercise 58.9 (16). -/
#check CircleMap.degree_power

/- Exercise 58.9 (17). -/
#check CircleMap.homotopic_of_degree_eq

/-- Exercise 58.9 (18). Two continuous circle maps are homotopic exactly when they have equal
degrees. -/
theorem CircleMap.homotopic_iff_degree_eq (orientation : Circle.FundamentalOrientation)
    (h k : C(Circle, Circle)) :
    h.Homotopic k ↔ CircleMap.degree orientation h = CircleMap.degree orientation k := by
  -- Combine homotopy invariance with the classification by degree.
  constructor
  · exact CircleMap.degree_eq_of_homotopic orientation h k
  · exact CircleMap.homotopic_of_degree_eq orientation h k
