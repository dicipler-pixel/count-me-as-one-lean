-- FALSE CONTROL: claims the figure-eight Alexander polynomial has a wall on S^1, at alpha = 0.
-- Delta_{4_1}(e^{2 pi i alpha}) = 3 - 2 cos(2 pi alpha) = 1 there, not 0.
import DiracTimeD25.AlexanderWall
open DiracTimeD25
theorem false_alex41_wall : alex41 (circ 0) = 0 := by
  rw [alex41_circle]; norm_num
