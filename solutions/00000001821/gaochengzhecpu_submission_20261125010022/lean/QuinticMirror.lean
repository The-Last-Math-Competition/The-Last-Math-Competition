import Std.Internal.Rat
import Std

namespace QuinticMirror

open Std.Internal (Rat)

abbrev Series := Array Rat

def rational (n : Nat) : Rat := ((n : Int) : Rat)

def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

def coefficient (s : Series) (n : Nat) : Rat := s[n]?.getD 0

def tabulate (precision : Nat) (f : Nat → Rat) : Series :=
  ((List.range (precision + 1)).map f).toArray

def sum (indices : List Nat) (f : Nat → Rat) : Rat :=
  indices.foldl (fun total i => total + f i) 0

def convolution (a b : Series) (n : Nat) : Rat :=
  sum (List.range (n + 1)) fun i => coefficient a i * coefficient b (n - i)

def product (precision : Nat) (a b : Series) : Series :=
  tabulate precision (convolution a b)

/-- The coefficients of 1/a, computed from a · (1/a) = 1. The input
    series used here all have nonzero constant coefficient. -/
def reciprocal (precision : Nat) (a : Series) : Series :=
  let a₀ := coefficient a 0
  (List.range precision).foldl (fun b k =>
    let n := k + 1
    let tail := sum (List.range n) fun j =>
      let i := j + 1
      coefficient a i * coefficient b (n - i)
    b.push (-tail / a₀)) #[(1 : Rat) / a₀]

/-- The coefficients of exp(a) for a series of zero constant term.
    Differentiation gives e_n = (∑ i*a_i*e_(n-i))/n. -/
def exponential (precision : Nat) (a : Series) : Series :=
  (List.range precision).foldl (fun e k =>
    let n := k + 1
    let total := sum (List.range n) fun j =>
      let i := j + 1
      rational i * coefficient a i * coefficient e (n - i)
    e.push (total / rational n)) #[1]

def periodCoefficient (n : Nat) : Rat :=
  rational (factorial (5*n)) / rational (factorial n ^ 5)

def logPeriodCoefficient (n : Nat) : Rat :=
  5 * periodCoefficient n *
    sum (List.range (4*n)) (fun j => 1 / rational (n + 1 + j))

/-- The period ratio G and the factor multiplying exp(-d G) in the
    residue formula for each positive-degree Yukawa coefficient. -/
def mirrorData (precision : Nat) : Series × Series :=
  let inversePeriod := reciprocal precision (tabulate precision periodCoefficient)
  let logarithm := product precision (tabulate precision logPeriodCoefficient) inversePeriod
  let logJacobian := tabulate precision fun n =>
    if n = 0 then 1 else rational n * coefficient logarithm n
  let inverseJacobian := reciprocal precision logJacobian
  let singlePole := tabulate precision fun n => rational (3125^n)
  let productOfInverses := product precision inversePeriod inverseJacobian
  let squared := product precision productOfInverses productOfInverses
  (logarithm, product precision singlePole squared)

def yukawaCoefficient (data : Series × Series) (d : Nat) : Rat :=
  let scaledLogarithm := tabulate d fun n => -rational d * coefficient data.1 n
  5 * convolution data.2 (exponential d scaledLogarithm) d

/-- The Lambert series extraction: c_d = ∑_(e|d) e³n_e.
    Slot zero is unused and is set to zero. -/
def instantonNumbers (precision : Nat) : Series :=
  let data := mirrorData precision
  (List.range precision).foldl (fun numbers k =>
    let d := k + 1
    let properDivisors := sum (List.range k) fun j =>
      let e := j + 1
      if d % e = 0 then rational (e^3) * coefficient numbers e else 0
    numbers.push ((yukawaCoefficient data d - properDivisors) / rational (d^3))) #[0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yukawaThroughDegreeSix : tabulate 6 (yukawaCoefficient (mirrorData 6)) =
    #[5, 2875, 4876875, 8564575000, 15517926796875, 28663236110956000,
      53621944306062201000] := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem computedThroughDegreeSix : instantonNumbers 6 =
    #[0, 2875, 609250, 317206375, 242467530000, 229305888887625, 248249742118022000] := by
  decide

theorem statedDegreeFiveFails : coefficient (instantonNumbers 6) 5 ≠ 317206375 := by
  rw [computedThroughDegreeSix]
  decide

theorem statedDegreeSixFails : coefficient (instantonNumbers 6) 6 ≠ 242467530000 := by
  rw [computedThroughDegreeSix]
  decide

#print axioms computedThroughDegreeSix
#print axioms yukawaThroughDegreeSix
#print axioms statedDegreeFiveFails
#print axioms statedDegreeSixFails

end QuinticMirror
