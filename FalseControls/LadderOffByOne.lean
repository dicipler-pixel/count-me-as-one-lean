-- FALSE CONTROL: claims five figure-eight monodromy turns stretch by 122 (it is 123 = phi^10 + phi^-10).
import FigureEightAnchors.Monodromy
open FigureEightAnchors.Monodromy
theorem false_trace5 : trace (pow41 5) = 122 := by decide
