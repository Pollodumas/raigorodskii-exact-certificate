import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ConcreteIdentityScratch

open Polynomial

abbrev F5 := ZMod 5

local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

def q5 : Polynomial F5 :=
  X ^ 6 + C 3 * X ^ 5 + C 2 * X ^ 4 + X ^ 2 + C 3 * X + C 1

def lin (a : F5) : Polynomial F5 := X + C a

def linQuot (a : F5) : Polynomial F5 :=
  X ^ 5 + C (3 - a) * X ^ 4 + C (a ^ 2 - 3 * a + 2) * X ^ 3
    + C (-a ^ 3 + 3 * a ^ 2 - 2 * a) * X ^ 2
    + C (a ^ 4 - 3 * a ^ 3 + 2 * a ^ 2 + 1) * X
    + C (-a ^ 5 + 3 * a ^ 4 - 2 * a ^ 3 - a + 3)

def linRem (a : F5) : F5 :=
  a ^ 6 - 3 * a ^ 5 + 2 * a ^ 4 + a ^ 2 - 3 * a + 1

lemma q5_lin_identity (a : F5) :
    q5 = lin a * linQuot a + C (linRem a) := by
  fin_cases a <;> native_decide


def quad (a b : F5) : Polynomial F5 :=
  X ^ 2 + C b * X + C a

def quadQuot (a b : F5) : Polynomial F5 :=
  X ^ 4 + C (3 - b) * X ^ 3 + C (-a + b ^ 2 - 3 * b + 2) * X ^ 2
    + C (2 * a * b - 3 * a - b ^ 3 + 3 * b ^ 2 - 2 * b) * X
    + C (a ^ 2 - 3 * a * b ^ 2 + 6 * a * b - 2 * a
      + b ^ 4 - 3 * b ^ 3 + 2 * b ^ 2 + 1)

def quadRem1 (a b : F5) : F5 :=
  -3 * a ^ 2 * b + 3 * a ^ 2 + 4 * a * b ^ 3 - 9 * a * b ^ 2
    + 4 * a * b - b ^ 5 + 3 * b ^ 4 - 2 * b ^ 3 - b + 3

def quadRem0 (a b : F5) : F5 :=
  -a ^ 3 + 3 * a ^ 2 * b ^ 2 - 6 * a ^ 2 * b + 2 * a ^ 2
    - a * b ^ 4 + 3 * a * b ^ 3 - 2 * a * b ^ 2 - a + 1

def quadRem (a b : F5) : Polynomial F5 :=
  C (quadRem1 a b) * X + C (quadRem0 a b)

lemma q5_quad_identity (a b : F5) :
    q5 = quad a b * quadQuot a b + quadRem a b := by
  fin_cases a <;> fin_cases b <;> native_decide


def cubic (a b c : F5) : Polynomial F5 :=
  X ^ 3 + C c * X ^ 2 + C b * X + C a

def cubicQuot (a b c : F5) : Polynomial F5 :=
  X ^ 3 + C (3 - c) * X ^ 2 + C (2 - b - 3 * c + c ^ 2) * X
    + C (-a + 2 * b * c - 3 * b - c ^ 3 + 3 * c ^ 2 - 2 * c)

def cubicRem2 (a b c : F5) : F5 :=
  2 * a * c - 3 * a + b ^ 2 - 3 * b * c ^ 2 + 6 * b * c - 2 * b
    + c ^ 4 - 3 * c ^ 3 + 2 * c ^ 2 + 1

def cubicRem1 (a b c : F5) : F5 :=
  2 * a * b - a * c ^ 2 + 3 * a * c - 2 * a - 2 * b ^ 2 * c
    + 3 * b ^ 2 + b * c ^ 3 - 3 * b * c ^ 2 + 2 * b * c + 3

def cubicRem0 (a b c : F5) : F5 :=
  a ^ 2 - 2 * a * b * c + 3 * a * b + a * c ^ 3 - 3 * a * c ^ 2
    + 2 * a * c + 1

def cubicRem (a b c : F5) : Polynomial F5 :=
  C (cubicRem2 a b c) * X ^ 2 + C (cubicRem1 a b c) * X + C (cubicRem0 a b c)

lemma q5_cubic_identity (a b c : F5) :
    q5 = cubic a b c * cubicQuot a b c + cubicRem a b c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> native_decide

end ConcreteIdentityScratch
