import Std
namespace PowerCells6685
open Lean.Grind
set_option maxHeartbeats 1000000
/-- There is no common power sphere over any characteristic-zero field,
in particular over the real numbers. No order or completeness is assumed. -/
theorem no_common_power_sphere {R : Type} [Field R] [IsCharP R 0]
  (x y z : R)
  (h1 : (x-1)*(x-1)+(y-1)*(y-1)+(z-1)*(z-1)-1/100 = x*x+y*y+z*z)
  (h2 : (x-1)*(x-1)+(y+1)*(y+1)+(z+1)*(z+1)-2/100 = x*x+y*y+z*z)
  (h3 : (x+1)*(x+1)+(y-1)*(y-1)+(z+1)*(z+1)-3/100 = x*x+y*y+z*z)
  (h4 : (x+1)*(x+1)+(y+1)*(y+1)+(z-1)*(z-1)-4/100 = x*x+y*y+z*z) : False := by
  grind

/-- Squared-distance differences are affine functions of the query point. -/
theorem power_difference_affine {R : Type} [Field R]
  (x y z a b c d e f u v : R) :
  ((x-a)*(x-a)+(y-b)*(y-b)+(z-c)*(z-c)-u) -
  ((x-d)*(x-d)+(y-e)*(y-e)+(z-f)*(z-f)-v) =
  2*x*(d-a)+2*y*(e-b)+2*z*(f-c) +
  (a*a+b*b+c*c-u)-(d*d+e*e+f*f-v) := by grind

end PowerCells6685
