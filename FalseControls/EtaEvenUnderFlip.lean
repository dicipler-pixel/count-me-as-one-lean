-- FALSE CONTROL: claims eta is EVEN under orientation reversal, eta(-D) = eta(D), for D = 1 (1x1).
-- eta(-D) = -eta(D) and eta(1) = 1, so this would need -1 = 1 in Z.
import DiracTimeD25.ChiralEta
open DiracTimeD25
theorem false_eta_even :
    eta (-(1 : Matrix (Fin 1) (Fin 1) ℂ)) Matrix.isHermitian_one.neg
      = eta (1 : Matrix (Fin 1) (Fin 1) ℂ) Matrix.isHermitian_one := by
  rw [eta_neg, eta_one]; decide
