import Velvet.Std
import Extensions.Testing
import Extensions.SpecDSL
import Extensions.VelvetPBT
import Mathlib.Tactic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

-- Problem: findExponents

section Specs

register_specdef_allow_recursion

def precondition (n : Nat) (primes : List Nat) : Prop :=
  n > 0 ∧
primes.length > 0 ∧
primes.all (fun p => Nat.Prime p) ∧
List.Nodup primes

instance instDecidablePrecond (n : Nat) (primes : List Nat) : Decidable (precondition n primes) := by
  unfold precondition
  infer_instance

def postcondition (n : Nat) (primes : List Nat) (result : List (Nat × Nat)) :=
  (n = result.foldl (fun acc (p, e) => acc * p ^ e) 1) ∧
result.all (fun (p, _) => p ∈ primes) ∧
primes.all (fun p => result.any (fun pair => pair.1 = p))

end Specs

section Impl

def findExponents (n : Nat) (primes : List Nat) : List (Nat × Nat) :=
  let rec countFactors (n : Nat) (primes : List Nat) : List (Nat × Nat) :=
    match primes with
    | [] => []
    | p :: ps =>
      let (count, n') :=
        countFactor n p 0
      (p, count) :: countFactors n' ps

  countFactors n primes
  where

  countFactor : Nat → Nat → Nat → Nat × Nat
  | 0, _, count =>
    (count, 0)
  | n, p, count =>
    if h : n > 0 ∧ p > 1 then
      have : n / p < n :=
        Nat.div_lt_self h.1 h.2
      if n % p == 0 then
        countFactor (n / p) p (count + 1)
      else
        (count, n)
    else
      (count, n)
  termination_by n _ _ => n

end Impl

section TestCases

def test1_n : Nat := 6
def test1_primes : List Nat := [2, 3]
def test1_Expected : List (Nat × Nat) := [(2, 1), (3, 1)]

def test2_n : Nat := 6285195213566005335561053533150026217291776
def test2_primes : List Nat := [2, 3, 5]
def test2_Expected : List (Nat × Nat) := [(2, 55), (3, 55), (5, 0)]

def test3_n : Nat := 360
def test3_primes : List Nat := [2, 3, 5]
def test3_Expected : List (Nat × Nat) := [(2, 3), (3, 2), (5, 1)]

def test4_n : Nat := 18903812908
def test4_primes : List Nat := [2, 43, 823, 133543]
def test4_Expected : List (Nat × Nat) := [(2, 2), (43, 1), (823, 1), (133543, 1)]

def test5_n : Nat := 114514
def test5_primes : List Nat := [2, 31, 1847]
def test5_Expected : List (Nat × Nat) := [(2, 1), (31, 1), (1847, 1)]

def test6_n : Nat := 20241147794175
def test6_primes : List Nat := [3, 5, 7, 11, 31, 47]
def test6_Expected : List (Nat × Nat) := [(3, 3), (5, 2), (7, 1), (11, 3), (31, 1), (47, 3)]

def test7_n : Nat := 6
def test7_primes : List Nat := [17]
def test7_Expected : List (Nat × Nat) := [(17, 0)]

def test8_n : Nat := 14
def test8_primes : List Nat := [17]
def test8_Expected : List (Nat × Nat) := [(17, 0)]

def test9_n : Nat := 12
def test9_primes : List Nat := [17]
def test9_Expected : List (Nat × Nat) := [(17, 0)]

def test10_n : Nat := 9
def test10_primes : List Nat := [19]
def test10_Expected : List (Nat × Nat) := [(19, 0)]

def test11_n : Nat := 10
def test11_primes : List Nat := [7]
def test11_Expected : List (Nat × Nat) := [(7, 0)]

def test12_n : Nat := 14
def test12_primes : List Nat := [19]
def test12_Expected : List (Nat × Nat) := [(19, 0)]

def test13_n : Nat := 17
def test13_primes : List Nat := [13]
def test13_Expected : List (Nat × Nat) := [(13, 0)]

def test14_n : Nat := 8
def test14_primes : List Nat := [5, 7]
def test14_Expected : List (Nat × Nat) := [(5, 0), (7, 0)]

def test15_n : Nat := 14
def test15_primes : List Nat := [17, 3]
def test15_Expected : List (Nat × Nat) := [(17, 0), (3, 0)]

def test16_n : Nat := 7
def test16_primes : List Nat := [2]
def test16_Expected : List (Nat × Nat) := [(2, 0)]

def test17_n : Nat := 12
def test17_primes : List Nat := [13, 2]
def test17_Expected : List (Nat × Nat) := [(13, 0), (2, 2)]

def test18_n : Nat := 7
def test18_primes : List Nat := [17, 13]
def test18_Expected : List (Nat × Nat) := [(17, 0), (13, 0)]

def test19_n : Nat := 12
def test19_primes : List Nat := [3]
def test19_Expected : List (Nat × Nat) := [(3, 1)]

def test20_n : Nat := 17
def test20_primes : List Nat := [11]
def test20_Expected : List (Nat × Nat) := [(11, 0)]

def test21_n : Nat := 15
def test21_primes : List Nat := [7]
def test21_Expected : List (Nat × Nat) := [(7, 0)]
end TestCases

set_option maxHeartbeats 500000

def uniqueness_test1'' (result : List (Nat × Nat)) :
  result ≠ test1_Expected →
  ¬ postcondition test1_n test1_primes result := by
  try dsimp at *
  plausible'_mut (seeds := #[test1_Expected]) (config := { numInst := 100000 })
