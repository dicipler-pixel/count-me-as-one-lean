-- FALSE CONTROL: claims the trefoil is its own mirror via the figure-eight's certificate.
import FigureEightAnchors.Chirality
open FigureEightAnchors.Chirality
theorem false_trefoil_amphichiral :
    mul (mul (tr P41) V31) P41 = neg (tr V31) := by decide
