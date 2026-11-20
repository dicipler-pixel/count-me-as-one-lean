-- FALSE CONTROL (D28 item 5): claims eta does not drift on 1/4 -> 3/4 (no crossing); it drifts by -1.
import D28.Easy
open DiracTimeD25
theorem false_no_drift : etaCircle (3 / 4) - etaCircle (1 / 4) = 0 := by
  rw [D28.etaCircle_three_quarter, etaCircle_quarter]; simp
