/-!
# Disproof of conjecture 00000001046

Verbatim conjecture: "The differential uniformity of `x ↦ x + x^{q−2}` is 2 for
large q (uniqueness of the optimal almost perfectly nonlinear (APN) function for
large q)".

Object discipline: `f : F_q → F_q`, `f x = x + x^{q−2}` over `F_q = GF(2^m)`;
for `x ≠ 0` this is `x + x⁻¹` and `f 0 = 0` (since `0^{q−2} = 0`).  Addition is
XOR (characteristic 2) and the differential uniformity is
`δ(f) = max_{a ≠ 0, b} #{x | f (x+a) + f x = b}` — exactly the map named in the
conjecture.

Attack: with input difference `a = 1` and output difference `b = 0`, the
preimage count is `4` for every even `m` (solutions are `x = 0`, `x = 1` and the
two roots of `x² + x + 1 = 0`, which exist in `F_{2^m}` iff `3 | 2^m − 1` iff
`m` is even).  Hence `δ ≥ 4 ≠ 2` at arbitrarily large `q`.  Below this is
certified on concrete fields: full enumeration at `q = 16` gives
`δ(f16) = 4` exactly, and the witness count `4` persists at `q = 256, 1024`.

Everything is table-driven and closed by `decide` on concrete `Nat` arithmetic:
no `sorry`, no `native_decide`; the axiom audit (`Check.lean`) reports that none
of the theorems depends on any axiom.
-/

namespace TLMC1046

/-!
### Axiom-free XOR encoding

`Nat.xor` (`^^^`) is implemented via well-founded recursion in core Lean, which
 drags `propext` into every `decide` that evaluates it.  We therefore use a
plain structural XOR on `k`-bit words: split into parity bits, combine with
`!=` (bit inequality = XOR), fold back.  For `k`-bit inputs this is *the*
bitwise XOR by construction.
-/

/-- Little-endian bits of `n`, `k` of them (structural in `k`). -/
def bitsOf : (k : Nat) → Nat → List Bool
  | 0, _ => []
  | k+1, n => (n % 2 == 1) :: bitsOf k (n / 2)

def fromBits : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * fromBits bs

def xorB : List Bool → List Bool → List Bool
  | [], bs => bs
  | bs, [] => bs
  | a :: as, b :: bs => (a != b) :: xorB as bs

/-- XOR of `x` and `y` as `k`-bit words (the bitwise XOR, axiom-free). -/
def xorn (k x y : Nat) : Nat := fromBits (xorB (bitsOf k x) (bitsOf k y))

/-- Structural list lookup (axiom-free under `decide`, unlike `List.getD`,
whose core definition drags `propext` into kernel reductions). -/
def latD2 : List α → Nat → α → α
  | [], _, v => v
  | a :: _, 0, _ => a
  | _ :: t, n+1, v => latD2 t n v

/-! ## GF(16): full differential-uniformity computation -/

/-- GF(16) multiplication table for `GF(2)[X]/(X⁴+X+1)`: entry `(x, y)`,
rows indexed by `x`, columns by `y` (both `0..15`). -/
def mul16 : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
  [0, 2, 4, 6, 8, 10, 12, 14, 3, 1, 7, 5, 11, 9, 15, 13],
  [0, 3, 6, 5, 12, 15, 10, 9, 11, 8, 13, 14, 7, 4, 1, 2],
  [0, 4, 8, 12, 3, 7, 11, 15, 6, 2, 14, 10, 5, 1, 13, 9],
  [0, 5, 10, 15, 7, 2, 13, 8, 14, 11, 4, 1, 9, 12, 3, 6],
  [0, 6, 12, 10, 11, 13, 7, 1, 5, 3, 9, 15, 14, 8, 2, 4],
  [0, 7, 14, 9, 15, 8, 1, 6, 13, 10, 3, 4, 2, 5, 12, 11],
  [0, 8, 3, 11, 6, 14, 5, 13, 12, 4, 15, 7, 10, 2, 9, 1],
  [0, 9, 1, 8, 2, 11, 3, 10, 4, 13, 5, 12, 6, 15, 7, 14],
  [0, 10, 7, 13, 14, 4, 9, 3, 15, 5, 8, 2, 1, 11, 6, 12],
  [0, 11, 5, 14, 10, 1, 15, 4, 7, 12, 2, 9, 13, 6, 8, 3],
  [0, 12, 11, 7, 5, 9, 14, 2, 10, 6, 1, 13, 15, 3, 4, 8],
  [0, 13, 9, 4, 1, 12, 8, 5, 2, 15, 11, 6, 3, 14, 10, 7],
  [0, 14, 15, 1, 13, 3, 2, 12, 9, 7, 6, 8, 4, 10, 11, 5],
  [0, 15, 13, 2, 9, 6, 4, 11, 1, 14, 12, 3, 8, 7, 5, 10]]

/-- GF(16) inversion table; `inv 0 = 0` by convention (matches `0^{q−2} = 0`). -/
def inv16 : List Nat := [0, 1, 9, 14, 13, 11, 7, 6, 15, 2, 12, 5, 10, 4, 3, 8]

def M16 (x y : Nat) : Nat := latD2 (latD2 mul16 x (List.replicate 16 0)) y 0
def I16 (x : Nat) : Nat := latD2 inv16 x 0

/-- `f x = x + x^{q−2}` on GF(16): `x + x⁻¹` for `x ≠ 0`, `f 0 = 0`
(addition = `xorn 4`, the 4-bit XOR). -/
def f16 (x : Nat) : Nat := xorn 4 x (I16 x)

/-- Number of `x` with `f (x + a) + f x = b` (XOR = addition in characteristic 2). -/
def cnt16 (a b : Nat) : Nat :=
  (List.range 16).countP (fun x => xorn 4 (f16 (xorn 4 x a)) (f16 x) == b)

/-- Every derivative value `b` is attained at most 4 times, for every nonzero
difference `a` (the differential uniformity quantifies over `a ≠ 0`; for
`a = 0` the derivative vanishes identically). -/
def bound16 : Bool :=
  (List.range' 1 15).all fun a => (List.range 16).all fun b => decide (cnt16 a b ≤ 4)

theorem bound16_true : bound16 = true := by decide

/-- Witness: `a = 1, b = 0` is attained 4 times (at `x = 0, 1, 6, 7`). -/
theorem cnt16_1_0 : cnt16 1 0 = 4 := by decide

theorem cnt16_1_0_ne_2 : cnt16 1 0 ≠ 2 := by decide

/-- The differential uniformity of `f16` is exactly `4`: every derivative value
occurs at most 4 times, and the value `4` is attained. -/
theorem delta16_eq_4 : (bound16 = true) ∧ (cnt16 1 0 = 4) :=
  ⟨bound16_true, cnt16_1_0⟩

/-! ## GF(256) and GF(1024): the failure persists at large `q` -/

/-- GF(2⁸) inversion table for `GF(2)[X]/(X⁸+X⁴+X³+X+1)` (0x11B), `inv 0 = 0`. -/
def inv256 : List Nat := [0, 1, 141, 246, 203, 82, 123, 209, 232, 79, 41, 192, 176, 225, 229, 199, 116, 180, 170, 75, 153, 43, 96, 95, 88, 63, 253, 204, 255, 64, 238, 178, 58, 110, 90, 241, 85, 77, 168, 201, 193, 10, 152, 21, 48, 68, 162, 194, 44, 69, 146, 108, 243, 57, 102, 66, 242, 53, 32, 111, 119, 187, 89, 25, 29, 254, 55, 103, 45, 49, 245, 105, 167, 100, 171, 19, 84, 37, 233, 9, 237, 92, 5, 202, 76, 36, 135, 191, 24, 62, 34, 240, 81, 236, 97, 23, 22, 94, 175, 211, 73, 166, 54, 67, 244, 71, 145, 223, 51, 147, 33, 59, 121, 183, 151, 133, 16, 181, 186, 60, 182, 112, 208, 6, 161, 250, 129, 130, 131, 126, 127, 128, 150, 115, 190, 86, 155, 158, 149, 217, 247, 2, 185, 164, 222, 106, 50, 109, 216, 138, 132, 114, 42, 20, 159, 136, 249, 220, 137, 154, 251, 124, 46, 195, 143, 184, 101, 72, 38, 200, 18, 74, 206, 231, 210, 98, 12, 224, 31, 239, 17, 117, 120, 113, 165, 142, 118, 61, 189, 188, 134, 87, 11, 40, 47, 163, 218, 212, 228, 15, 169, 39, 83, 4, 27, 252, 172, 230, 122, 7, 174, 99, 197, 219, 226, 234, 148, 139, 196, 213, 157, 248, 144, 107, 177, 13, 214, 235, 198, 14, 207, 173, 8, 78, 215, 227, 93, 80, 30, 179, 91, 35, 56, 52, 104, 70, 3, 140, 221, 156, 125, 160, 205, 26, 65, 28]

def I256 (x : Nat) : Nat := latD2 inv256 x 0

/-- `f x = x + x^{q−2}` on GF(2⁸) (addition = `xorn 8`, the 8-bit XOR). -/
def f256 (x : Nat) : Nat := xorn 8 x (I256 x)

def cnt256 (a b : Nat) : Nat :=
  (List.range 256).countP (fun x => xorn 8 (f256 (xorn 8 x a)) (f256 x) == b)

set_option maxRecDepth 65536 in
theorem cnt256_1_0 : cnt256 1 0 = 4 := by decide
set_option maxRecDepth 65536 in
theorem cnt256_1_0_ne_2 : cnt256 1 0 ≠ 2 := by decide

/-- GF(2¹⁰) inversion table for `GF(2)[X]/(X¹⁰+X³+1)` (0x409), `inv 0 = 0`. -/
def inv1024 : List Nat := [0, 1, 516, 1016, 258, 687, 508, 734, 129, 589, 851, 184, 254, 232, 367, 610, 580, 478, 802, 214, 941, 242, 92, 88, 127, 977, 116, 572, 691, 104, 305, 399, 290, 133, 239, 765, 401, 632, 107, 991, 978, 423, 121, 335, 46, 531, 44, 530, 571, 395, 1004, 845, 58, 949, 286, 231, 861, 975, 52, 948, 668, 1001, 707, 937, 145, 359, 582, 135, 627, 473, 890, 672, 716, 738, 316, 325, 561, 364, 1003, 296, 489, 253, 727, 894, 568, 315, 675, 563, 23, 93, 781, 308, 22, 89, 265, 660, 793, 629, 705, 900, 502, 427, 930, 310, 29, 690, 990, 38, 143, 337, 631, 559, 938, 521, 995, 574, 26, 573, 474, 497, 334, 42, 1008, 157, 869, 197, 976, 24, 588, 8, 695, 747, 291, 33, 583, 67, 829, 810, 744, 993, 445, 908, 336, 108, 358, 64, 369, 512, 158, 490, 678, 819, 796, 175, 182, 206, 1009, 123, 148, 491, 752, 319, 634, 467, 879, 380, 447, 240, 284, 789, 665, 872, 853, 766, 797, 153, 527, 485, 554, 288, 898, 710, 154, 207, 11, 850, 552, 617, 640, 997, 330, 952, 904, 914, 830, 221, 868, 125, 450, 608, 251, 615, 721, 741, 465, 515, 155, 183, 522, 799, 345, 943, 495, 1006, 19, 803, 579, 784, 684, 601, 831, 195, 787, 482, 469, 396, 768, 564, 1013, 279, 287, 55, 13, 255, 794, 972, 237, 236, 764, 34, 167, 446, 21, 940, 504, 298, 586, 983, 950, 534, 614, 200, 488, 81, 12, 233, 294, 928, 4, 686, 863, 416, 881, 968, 661, 94, 532, 498, 807, 959, 549, 719, 922, 441, 405, 877, 372, 356, 1012, 229, 730, 333, 454, 677, 168, 788, 54, 230, 179, 555, 32, 132, 700, 492, 256, 929, 79, 1002, 245, 505, 339, 911, 925, 778, 398, 30, 595, 500, 91, 780, 103, 931, 1020, 944, 569, 85, 74, 324, 753, 161, 376, 743, 667, 649, 317, 75, 749, 409, 947, 551, 190, 953, 731, 281, 120, 43, 142, 109, 910, 300, 840, 645, 436, 518, 942, 210, 383, 477, 906, 419, 584, 413, 771, 857, 758, 362, 277, 373, 144, 65, 449, 751, 355, 759, 77, 560, 611, 14, 513, 146, 425, 754, 276, 357, 816, 896, 320, 742, 1014, 708, 165, 878, 476, 346, 452, 697, 457, 1023, 415, 606, 618, 965, 434, 966, 570, 49, 225, 468, 304, 31, 633, 36, 823, 885, 876, 274, 886, 643, 748, 327, 773, 737, 585, 351, 607, 388, 261, 862, 907, 349, 680, 955, 979, 41, 755, 370, 503, 101, 525, 957, 917, 834, 805, 926, 392, 967, 342, 519, 808, 762, 923, 273, 613, 812, 909, 140, 241, 166, 750, 360, 198, 609, 384, 696, 282, 676, 1022, 386, 655, 713, 651, 544, 543, 866, 514, 204, 635, 163, 397, 224, 486, 688, 626, 69, 118, 496, 382, 347, 17, 581, 599, 761, 223, 786, 526, 177, 470, 689, 252, 80, 149, 159, 293, 701, 1007, 212, 475, 119, 267, 533, 307, 594, 100, 426, 244, 299, 556, 756, 6, 735, 624, 912, 147, 368, 464, 205, 2, 1017, 343, 437, 939, 113, 208, 798, 956, 428, 484, 176, 846, 670, 47, 45, 266, 499, 249, 951, 919, 865, 987, 859, 790, 659, 867, 462, 461, 650, 728, 592, 718, 270, 946, 329, 186, 616, 178, 289, 506, 757, 630, 111, 365, 76, 674, 87, 227, 769, 854, 620, 84, 314, 394, 48, 27, 117, 115, 994, 605, 971, 785, 216, 16, 479, 66, 134, 350, 412, 246, 982, 128, 9, 980, 623, 547, 729, 501, 306, 638, 934, 760, 480, 685, 219, 963, 889, 970, 576, 389, 414, 199, 451, 15, 366, 813, 442, 250, 201, 553, 187, 390, 964, 567, 855, 981, 591, 510, 913, 472, 68, 792, 97, 558, 110, 37, 400, 162, 466, 892, 849, 596, 935, 188, 996, 887, 407, 841, 341, 832, 921, 666, 323, 545, 460, 882, 723, 712, 458, 989, 1010, 791, 541, 95, 264, 984, 843, 873, 170, 648, 322, 60, 1000, 529, 847, 71, 891, 562, 86, 455, 283, 150, 818, 420, 954, 838, 826, 218, 600, 259, 5, 471, 487, 105, 28, 699, 724, 746, 130, 453, 385, 725, 692, 292, 493, 714, 777, 901, 98, 936, 62, 379, 1015, 181, 899, 654, 459, 702, 776, 72, 739, 548, 271, 740, 202, 883, 653, 693, 698, 895, 82, 546, 593, 280, 332, 821, 903, 7, 509, 772, 411, 73, 717, 720, 203, 377, 321, 138, 992, 694, 131, 408, 326, 448, 361, 160, 318, 371, 424, 507, 557, 354, 363, 598, 481, 439, 809, 238, 35, 173, 852, 226, 565, 856, 352, 736, 410, 1019, 874, 715, 703, 303, 924, 309, 90, 998, 871, 217, 578, 483, 222, 285, 169, 540, 658, 628, 96, 234, 973, 152, 174, 523, 209, 824, 933, 18, 215, 927, 432, 958, 268, 438, 763, 137, 828, 443, 612, 837, 960, 374, 897, 679, 151, 902, 732, 884, 402, 800, 932, 683, 839, 811, 136, 194, 220, 646, 920, 431, 916, 961, 814, 682, 827, 340, 644, 985, 663, 1005, 51, 528, 671, 893, 637, 185, 10, 767, 172, 566, 621, 770, 353, 986, 539, 974, 56, 417, 260, 918, 537, 463, 542, 196, 124, 999, 783, 171, 664, 775, 1018, 404, 275, 381, 164, 969, 262, 652, 722, 822, 403, 406, 642, 962, 603, 70, 673, 636, 848, 83, 726, 375, 817, 180, 711, 99, 704, 820, 733, 192, 915, 348, 418, 141, 444, 338, 301, 511, 625, 193, 905, 835, 430, 864, 536, 833, 647, 272, 440, 779, 302, 433, 804, 257, 295, 102, 311, 825, 801, 597, 639, 706, 63, 112, 520, 243, 20, 344, 211, 313, 1021, 550, 328, 59, 53, 248, 535, 191, 331, 681, 421, 524, 429, 806, 269, 815, 836, 888, 602, 619, 391, 393, 435, 263, 880, 604, 577, 235, 795, 860, 57, 126, 25, 40, 422, 590, 622, 587, 247, 662, 842, 858, 538, 1011, 656, 106, 39, 745, 139, 575, 114, 641, 189, 782, 870, 669, 61, 297, 78, 50, 844, 213, 494, 122, 156, 657, 988, 278, 228, 378, 709, 3, 517, 875, 774, 312, 945, 456, 387]

def I1024 (x : Nat) : Nat := latD2 inv1024 x 0

/-- `f x = x + x^{q−2}` on GF(2¹⁰) (addition = `xorn 10`, the 10-bit XOR). -/
def f1024 (x : Nat) : Nat := xorn 10 x (I1024 x)

def cnt1024 (a b : Nat) : Nat :=
  (List.range 1024).countP (fun x => xorn 10 (f1024 (xorn 10 x a)) (f1024 x) == b)

-- the getD lookups over the 1024-entry table recurse ~1024 deep during
-- elaboration-time evaluation, so elaborator limits must be raised
-- (compiler limits only; the proofs stay `decide`-based and axiom-free)
set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
theorem cnt1024_1_0 : cnt1024 1 0 = 4 := by decide
set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
theorem cnt1024_1_0_ne_2 : cnt1024 1 0 ≠ 2 := by decide

/-- Main disproof exhibit: `δ = 4` exactly at `q = 16` (full enumeration), and
the derivative value `4` still occurs at `q = 256` and `q = 1024`, so the
conjectured value `2` fails there. -/
theorem disproof :
    (cnt16 1 0 = 4) ∧ (cnt256 1 0 = 4) ∧ (cnt1024 1 0 = 4) :=
  ⟨cnt16_1_0, cnt256_1_0, cnt1024_1_0⟩

end TLMC1046
