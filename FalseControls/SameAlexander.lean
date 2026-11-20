-- FALSE CONTROL: claims 4_1 and 3_1 share an Alexander polynomial.
import FigureEightAnchors.Chirality
open FigureEightAnchors.Chirality
theorem false_same_alex : alex V41 = alex V31 := by decide
