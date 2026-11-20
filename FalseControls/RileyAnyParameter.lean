-- FALSE CONTROL: claims the Riley relation holds at c = 1 (needs c^2 - c + 1 = 0; 1 - 1 + 1 = 1).
import FigureEightAnchors.Riley
open FigureEightAnchors.Riley
theorem false_riley_c1 :
    mul (W (1 : Int)) A = mul (B 1) (W 1) := by decide
