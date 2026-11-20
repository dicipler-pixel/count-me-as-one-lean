-- FALSE CONTROL: claims the integer shape z = w = 2 solves Thurston's edge equation (gives 3, not 0).
import FigureEightAnchors.Gluing
open FigureEightAnchors.Gluing
theorem false_edge_two : edge (2 : Int) 2 = 0 := by decide
