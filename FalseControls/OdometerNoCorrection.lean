-- FALSE CONTROL: claims the circle eta term vanishes at a = 1/4 (no boundary correction in DT-E15).
-- etaCircle (1/4) = 1 - 2 * (1/4) = 1/2, not 0.
import DiracTimeD25.CircleOdometer
open DiracTimeD25
theorem false_etaCircle_quarter : etaCircle (1 / 4) = 0 := by
  rw [etaCircle_quarter]; simp
