import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LinIdentityScratch

open Polynomial

noncomputable section

abbrev F5 := ZMod 5
local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

noncomputable def q5 : Polynomial F5 :=
  X ^ 6 + C 3 * X ^ 5 + C 2 * X ^ 4 + X ^ 2 + C 3 * X + C 1

noncomputable def lin (a : F5) : Polynomial F5 := X + C a

noncomputable def linQuot (a : F5) : Polynomial F5 :=
  X ^ 5 + C (3 - a) * X ^ 4 + C (a ^ 2 - 3 * a + 2) * X ^ 3
    + C (-a ^ 3 + 3 * a ^ 2 - 2 * a) * X ^ 2
    + C (a ^ 4 - 3 * a ^ 3 + 2 * a ^ 2 + 1) * X
    + C (-a ^ 5 + 3 * a ^ 4 - 2 * a ^ 3 - a + 3)

def linRem (a : F5) : F5 :=
  a ^ 6 - 3 * a ^ 5 + 2 * a ^ 4 + a ^ 2 - 3 * a + 1

lemma q5_lin_identity (a : F5) :
    q5 = lin a * linQuot a + C (linRem a) := by
  fin_cases a <;>
    ext (_ | _ | _ | _ | _ | _ | _ | n) <;>
    simp [q5, lin, linQuot, linRem, coeff_mul] <;> norm_num

end
end LinIdentityScratch
