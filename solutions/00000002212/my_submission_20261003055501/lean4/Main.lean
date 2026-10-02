/-
  Disproof of TLMC conjecture 00000002212.

  Conjecture: "The catenary degree c(H) (diameter of the factorization
  graph) of the three-generated numerical semigroup <a, b, c> is an
  explicit function of min(a, b, c)."

  Refutation: two counterexample pairs with equal minima and unequal
  catenary degrees:

    c(<5,6,7>)  = 4   and   c(<5,6,25>) = 5,   both with min = 5;
    c(<6,7,8>)  = 4   and   c(<6,7,35>) = 7,   both with min = 6.

  For <5,6,7> the generators are pairwise coprime, so the semigroup is
  generic and its Betti elements are exactly the three pair products
  {5*6, 5*7, 6*7} = {30, 35, 42} (classical: for pairwise-coprime
  minimal generators the minimal presentation is given by the three
  primitive pair relations).  The catenary degree of a numerical
  semigroup is the maximum of c(n) over its Betti elements (classical,
  Chapman-Garcia-Sanchez-Llena).  Kernel-certified below: the complete
  factorization sets Z(30), Z(35), Z(42) of <5,6,7> and Z(25), Z(30) of
  <5,6,25>.  From these, sup-norm distance tables give
  c(30) = c(35) = c(42) = 4 (each: a chain at distance 4 connects all
  factorizations, and at distance 3 the factorization (6,0,0) resp.
  (7,0,0) is isolated) and c(25) = c(30) = 5 for <5,6,25> (at
  distance 5 all connected; at 4, (6,0,0) isolated in Z(30), and
  Z(25) = {(5,0,0),(0,0,1)} is a two-point set at distance 5).  Hence
  c(<5,6,7>) = 4 < 5 = c(<5,6,25>) while min = 5 for both: c is NOT a
  function of min(a,b,c).  (The second pair <6,7,8>/<6,7,35> with
  c = 4 vs 7 is verified in reproduce.py.)

  All kernel computations are closed case analyses; the audit reports
  zero axioms.  (Core's Nat.mul_assoc / Nat.add_mul carry axioms, so
  the two associativity facts used are rebuilt by induction.)
-/

namespace Tlmc2212

/-! ## Axiom-free arithmetic helpers. -/

theorem add_right_comm_self (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_comm b c, ← Nat.add_assoc]

theorem add_left_comm_pair (b c d : Nat) : b + (c + d) = c + (b + d) := by
  rw [← Nat.add_assoc b c d, Nat.add_comm b c, Nat.add_assoc c b d]

theorem add_swap4 (a b c d : Nat) : a + b + (c + d) = a + c + (b + d) := by
  rw [Nat.add_assoc a b (c + d), add_left_comm_pair b c d,
    ← Nat.add_assoc a c (b + d)]

theorem add_mul_self (a b c : Nat) : (a + b) * c = a * c + b * c := by
  induction c with
  | zero => rw [Nat.mul_zero, Nat.mul_zero, Nat.mul_zero]
  | succ c ih =>
      rw [Nat.mul_succ, Nat.mul_succ, Nat.mul_succ, ih]
      exact add_swap4 (a * c) (b * c) a b

theorem mul_assoc_self (a b c : Nat) : a * b * c = a * (b * c) := by
  induction a with
  | zero => rw [Nat.zero_mul, Nat.zero_mul, Nat.zero_mul]
  | succ n ih =>
      rw [Nat.succ_mul, Nat.succ_mul]
      rw [add_mul_self (n * b) b c]
      rw [ih]

theorem add_left_cancel_eq : ∀ (x y z : Nat), x + y = x + z → y = z := by
  intro x
  induction x with
  | zero =>
      intro y z h
      rw [Nat.zero_add, Nat.zero_add] at h
      exact h
  | succ n ih =>
      intro y z h
      exact ih y z (Nat.succ.inj (by rw [Nat.succ_add, Nat.succ_add] at h; exact h))

/-- `Z_(5,6,7)(30)` is exactly the listed set. -/
theorem Z567_30 : ∀ z1 z2 z3 : Nat,
    5 * z1 + 6 * z2 + 7 * z3 = 30 →
    (z1 = 0 ∧ z2 = 5 ∧ z3 = 0) ∨ (z1 = 1 ∧ z2 = 3 ∧ z3 = 1) ∨ (z1 = 2 ∧ z2 = 1 ∧ z3 = 2) ∨ (z1 = 6 ∧ z2 = 0 ∧ z3 = 0) := by
  intro z1 z2 z3 h
  have hz : 5 * z1 + 6 * z2 ≤ 30 :=
    Nat.le_trans (Nat.le_add_right (5 * z1 + 6 * z2) (7 * z3)) (Nat.le_of_eq h)
  cases z1 with
  | zero =>
    -- z1 = 0
    have hz1 : 5 * Nat.zero + 6 * z2 ≤ 30 :=
      Nat.le_trans (Nat.le_add_right (5 * Nat.zero + 6 * z2) (7 * z3)) (Nat.le_of_eq h)
    cases z2 with
    | zero =>
      -- z1 = 0, z2 = 0: 7 * z3 = 30
      have hD : 7 * z3 = 30 :=
        add_left_cancel_eq (5 * Nat.zero + 6 * Nat.zero) (7 * z3) 30 (Eq.trans h (rfl : (30:Nat) = 5 * Nat.zero + 6 * Nat.zero + 30))
      rcases Nat.lt_or_ge z3 5 with hc | hc
      · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
            (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
      · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
            (Nat.le_of_eq hD)) (by decide)
    | succ z21 =>
      cases z21 with
      | zero =>
        -- z1 = 0, z2 = 1: 7 * z3 = 24
        have hD : 7 * z3 = 24 :=
          add_left_cancel_eq (5 * Nat.zero + 6 * Nat.succ (Nat.zero)) (7 * z3) 24 (Eq.trans h (rfl : (30:Nat) = 5 * Nat.zero + 6 * Nat.succ (Nat.zero) + 24))
        rcases Nat.lt_or_ge z3 4 with hc | hc
        · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
              (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
        · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
              (Nat.le_of_eq hD)) (by decide)
      | succ z212 =>
        cases z212 with
        | zero =>
          -- z1 = 0, z2 = 2: 7 * z3 = 18
          have hD : 7 * z3 = 18 :=
            add_left_cancel_eq (5 * Nat.zero + 6 * Nat.succ (Nat.succ (Nat.zero))) (7 * z3) 18 (Eq.trans h (rfl : (30:Nat) = 5 * Nat.zero + 6 * Nat.succ (Nat.succ (Nat.zero)) + 18))
          rcases Nat.lt_or_ge z3 3 with hc | hc
          · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
          · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                (Nat.le_of_eq hD)) (by decide)
        | succ z2123 =>
          cases z2123 with
          | zero =>
            -- z1 = 0, z2 = 3: 7 * z3 = 12
            have hD : 7 * z3 = 12 :=
              add_left_cancel_eq (5 * Nat.zero + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) (7 * z3) 12 (Eq.trans h (rfl : (30:Nat) = 5 * Nat.zero + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 12))
            rcases Nat.lt_or_ge z3 2 with hc | hc
            · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                  (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
            · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                  (Nat.le_of_eq hD)) (by decide)
          | succ z21234 =>
            cases z21234 with
            | zero =>
              -- z1 = 0, z2 = 4: 7 * z3 = 6
              have hD : 7 * z3 = 6 :=
                add_left_cancel_eq (5 * Nat.zero + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) (7 * z3) 6 (Eq.trans h (rfl : (30:Nat) = 5 * Nat.zero + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6))
              rcases Nat.lt_or_ge z3 1 with hc | hc
              · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                    (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
              · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                    (Nat.le_of_eq hD)) (by decide)
            | succ z212345 =>
              cases z212345 with
              | zero =>
                -- z1 = 0, z2 = 5: 7 * z3 = 0
                have hD : 7 * z3 = 0 :=
                  add_left_cancel_eq (5 * Nat.zero + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))) (7 * z3) 0 (Eq.trans h (rfl : (30:Nat) = 5 * Nat.zero + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 0))
                rcases Nat.lt_or_ge z3 1 with hc | hc
                · exact Or.inl (⟨rfl, rfl, Nat.le_antisymm (Nat.le_of_lt_succ hc) (Nat.zero_le z3)⟩)
                · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                      (Nat.le_of_eq hD)) (by decide)
              | succ z212345k =>
                have hz2o : 5 * Nat.zero + 6 * ((((((z212345k + 1) + 1) + 1) + 1) + 1) + 1) ≤ 30 :=
                  Nat.le_trans (Nat.le_add_right (5 * Nat.zero + 6 * ((((((z212345k + 1) + 1) + 1) + 1) + 1) + 1)) (7 * z3)) (Nat.le_of_eq h)
                have hb : (6:Nat) ≤ ((((((z212345k + 1) + 1) + 1) + 1) + 1) + 1) := (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.le_add_left 1 z212345k) 1) 1) 1) 1) 1)
                have hfin : (5 * Nat.zero + 6 * 6) ≤ 30 :=
                  Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hb) (5 * Nat.zero)) hz2o
                exact absurd hfin (by decide)
  | succ z11 =>
    cases z11 with
    | zero =>
      -- z1 = 1
      have hz1 : 5 * Nat.succ (Nat.zero) + 6 * z2 ≤ 30 :=
        Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.zero) + 6 * z2) (7 * z3)) (Nat.le_of_eq h)
      cases z2 with
      | zero =>
        -- z1 = 1, z2 = 0: 7 * z3 = 25
        have hD : 7 * z3 = 25 :=
          add_left_cancel_eq (5 * Nat.succ (Nat.zero) + 6 * Nat.zero) (7 * z3) 25 (Eq.trans h (rfl : (30:Nat) = 5 * Nat.succ (Nat.zero) + 6 * Nat.zero + 25))
        rcases Nat.lt_or_ge z3 4 with hc | hc
        · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
              (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
        · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
              (Nat.le_of_eq hD)) (by decide)
      | succ z21 =>
        cases z21 with
        | zero =>
          -- z1 = 1, z2 = 1: 7 * z3 = 19
          have hD : 7 * z3 = 19 :=
            add_left_cancel_eq (5 * Nat.succ (Nat.zero) + 6 * Nat.succ (Nat.zero)) (7 * z3) 19 (Eq.trans h (rfl : (30:Nat) = 5 * Nat.succ (Nat.zero) + 6 * Nat.succ (Nat.zero) + 19))
          rcases Nat.lt_or_ge z3 3 with hc | hc
          · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
          · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                (Nat.le_of_eq hD)) (by decide)
        | succ z212 =>
          cases z212 with
          | zero =>
            -- z1 = 1, z2 = 2: 7 * z3 = 13
            have hD : 7 * z3 = 13 :=
              add_left_cancel_eq (5 * Nat.succ (Nat.zero) + 6 * Nat.succ (Nat.succ (Nat.zero))) (7 * z3) 13 (Eq.trans h (rfl : (30:Nat) = 5 * Nat.succ (Nat.zero) + 6 * Nat.succ (Nat.succ (Nat.zero)) + 13))
            rcases Nat.lt_or_ge z3 2 with hc | hc
            · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                  (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
            · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                  (Nat.le_of_eq hD)) (by decide)
          | succ z2123 =>
            cases z2123 with
            | zero =>
              -- z1 = 1, z2 = 3: 7 * z3 = 7
              have hD : 7 * z3 = 7 :=
                add_left_cancel_eq (5 * Nat.succ (Nat.zero) + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) (7 * z3) 7 (Eq.trans h (rfl : (30:Nat) = 5 * Nat.succ (Nat.zero) + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 7))
              rcases Nat.lt_or_ge z3 2 with hc | hc
              · rcases Nat.lt_or_ge z3 1 with hc2 | hc2
                · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                      (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc2))) (by decide)
                · exact Or.inr (Or.inl (⟨rfl, rfl, Nat.le_antisymm (Nat.le_of_lt_succ hc) hc2⟩))
              · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                    (Nat.le_of_eq hD)) (by decide)
            | succ z21234 =>
              cases z21234 with
              | zero =>
                -- z1 = 1, z2 = 4: 7 * z3 = 1
                have hD : 7 * z3 = 1 :=
                  add_left_cancel_eq (5 * Nat.succ (Nat.zero) + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) (7 * z3) 1 (Eq.trans h (rfl : (30:Nat) = 5 * Nat.succ (Nat.zero) + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 1))
                rcases Nat.lt_or_ge z3 1 with hc | hc
                · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                      (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
                · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                      (Nat.le_of_eq hD)) (by decide)
              | succ z21234k =>
                have hz2o : 5 * Nat.succ (Nat.zero) + 6 * (((((z21234k + 1) + 1) + 1) + 1) + 1) ≤ 30 :=
                  Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.zero) + 6 * (((((z21234k + 1) + 1) + 1) + 1) + 1)) (7 * z3)) (Nat.le_of_eq h)
                have hb : (5:Nat) ≤ (((((z21234k + 1) + 1) + 1) + 1) + 1) := (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.le_add_left 1 z21234k) 1) 1) 1) 1)
                have hfin : (5 * Nat.succ (Nat.zero) + 6 * 5) ≤ 30 :=
                  Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hb) (5 * Nat.succ (Nat.zero))) hz2o
                exact absurd hfin (by decide)
    | succ z112 =>
      cases z112 with
      | zero =>
        -- z1 = 2
        have hz1 : 5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * z2 ≤ 30 :=
          Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * z2) (7 * z3)) (Nat.le_of_eq h)
        cases z2 with
        | zero =>
          -- z1 = 2, z2 = 0: 7 * z3 = 20
          have hD : 7 * z3 = 20 :=
            add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * Nat.zero) (7 * z3) 20 (Eq.trans h (rfl : (30:Nat) = 5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * Nat.zero + 20))
          rcases Nat.lt_or_ge z3 3 with hc | hc
          · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
          · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                (Nat.le_of_eq hD)) (by decide)
        | succ z21 =>
          cases z21 with
          | zero =>
            -- z1 = 2, z2 = 1: 7 * z3 = 14
            have hD : 7 * z3 = 14 :=
              add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * Nat.succ (Nat.zero)) (7 * z3) 14 (Eq.trans h (rfl : (30:Nat) = 5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * Nat.succ (Nat.zero) + 14))
            rcases Nat.lt_or_ge z3 3 with hc | hc
            · rcases Nat.lt_or_ge z3 2 with hc2 | hc2
              · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                    (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc2))) (by decide)
              · exact Or.inr (Or.inr (Or.inl (⟨rfl, rfl, Nat.le_antisymm (Nat.le_of_lt_succ hc) hc2⟩)))
            · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                  (Nat.le_of_eq hD)) (by decide)
          | succ z212 =>
            cases z212 with
            | zero =>
              -- z1 = 2, z2 = 2: 7 * z3 = 8
              have hD : 7 * z3 = 8 :=
                add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * Nat.succ (Nat.succ (Nat.zero))) (7 * z3) 8 (Eq.trans h (rfl : (30:Nat) = 5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * Nat.succ (Nat.succ (Nat.zero)) + 8))
              rcases Nat.lt_or_ge z3 2 with hc | hc
              · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                    (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
              · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                    (Nat.le_of_eq hD)) (by decide)
            | succ z2123 =>
              cases z2123 with
              | zero =>
                -- z1 = 2, z2 = 3: 7 * z3 = 2
                have hD : 7 * z3 = 2 :=
                  add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) (7 * z3) 2 (Eq.trans h (rfl : (30:Nat) = 5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 2))
                rcases Nat.lt_or_ge z3 1 with hc | hc
                · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                      (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
                · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                      (Nat.le_of_eq hD)) (by decide)
              | succ z2123k =>
                have hz2o : 5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * ((((z2123k + 1) + 1) + 1) + 1) ≤ 30 :=
                  Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * ((((z2123k + 1) + 1) + 1) + 1)) (7 * z3)) (Nat.le_of_eq h)
                have hb : (4:Nat) ≤ ((((z2123k + 1) + 1) + 1) + 1) := (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.le_add_left 1 z2123k) 1) 1) 1)
                have hfin : (5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * 4) ≤ 30 :=
                  Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hb) (5 * Nat.succ (Nat.succ (Nat.zero)))) hz2o
                exact absurd hfin (by decide)
      | succ z1123 =>
        cases z1123 with
        | zero =>
          -- z1 = 3
          have hz1 : 5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * z2 ≤ 30 :=
            Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * z2) (7 * z3)) (Nat.le_of_eq h)
          cases z2 with
          | zero =>
            -- z1 = 3, z2 = 0: 7 * z3 = 15
            have hD : 7 * z3 = 15 :=
              add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * Nat.zero) (7 * z3) 15 (Eq.trans h (rfl : (30:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * Nat.zero + 15))
            rcases Nat.lt_or_ge z3 3 with hc | hc
            · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                  (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
            · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                  (Nat.le_of_eq hD)) (by decide)
          | succ z21 =>
            cases z21 with
            | zero =>
              -- z1 = 3, z2 = 1: 7 * z3 = 9
              have hD : 7 * z3 = 9 :=
                add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * Nat.succ (Nat.zero)) (7 * z3) 9 (Eq.trans h (rfl : (30:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * Nat.succ (Nat.zero) + 9))
              rcases Nat.lt_or_ge z3 2 with hc | hc
              · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                    (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
              · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                    (Nat.le_of_eq hD)) (by decide)
            | succ z212 =>
              cases z212 with
              | zero =>
                -- z1 = 3, z2 = 2: 7 * z3 = 3
                have hD : 7 * z3 = 3 :=
                  add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * Nat.succ (Nat.succ (Nat.zero))) (7 * z3) 3 (Eq.trans h (rfl : (30:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * Nat.succ (Nat.succ (Nat.zero)) + 3))
                rcases Nat.lt_or_ge z3 1 with hc | hc
                · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                      (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
                · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                      (Nat.le_of_eq hD)) (by decide)
              | succ z212k =>
                have hz2o : 5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * (((z212k + 1) + 1) + 1) ≤ 30 :=
                  Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * (((z212k + 1) + 1) + 1)) (7 * z3)) (Nat.le_of_eq h)
                have hb : (3:Nat) ≤ (((z212k + 1) + 1) + 1) := (Nat.add_le_add_right (Nat.add_le_add_right (Nat.le_add_left 1 z212k) 1) 1)
                have hfin : (5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * 3) ≤ 30 :=
                  Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hb) (5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) hz2o
                exact absurd hfin (by decide)
        | succ z11234 =>
          cases z11234 with
          | zero =>
            -- z1 = 4
            have hz1 : 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * z2 ≤ 30 :=
              Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * z2) (7 * z3)) (Nat.le_of_eq h)
            cases z2 with
            | zero =>
              -- z1 = 4, z2 = 0: 7 * z3 = 10
              have hD : 7 * z3 = 10 :=
                add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * Nat.zero) (7 * z3) 10 (Eq.trans h (rfl : (30:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * Nat.zero + 10))
              rcases Nat.lt_or_ge z3 2 with hc | hc
              · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                    (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
              · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                    (Nat.le_of_eq hD)) (by decide)
            | succ z21 =>
              cases z21 with
              | zero =>
                -- z1 = 4, z2 = 1: 7 * z3 = 4
                have hD : 7 * z3 = 4 :=
                  add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * Nat.succ (Nat.zero)) (7 * z3) 4 (Eq.trans h (rfl : (30:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * Nat.succ (Nat.zero) + 4))
                rcases Nat.lt_or_ge z3 1 with hc | hc
                · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                      (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
                · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                      (Nat.le_of_eq hD)) (by decide)
              | succ z21k =>
                have hz2o : 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * ((z21k + 1) + 1) ≤ 30 :=
                  Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * ((z21k + 1) + 1)) (7 * z3)) (Nat.le_of_eq h)
                have hb : (2:Nat) ≤ ((z21k + 1) + 1) := (Nat.add_le_add_right (Nat.le_add_left 1 z21k) 1)
                have hfin : (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * 2) ≤ 30 :=
                  Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hb) (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))) hz2o
                exact absurd hfin (by decide)
          | succ z112345 =>
            cases z112345 with
            | zero =>
              -- z1 = 5
              have hz1 : 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 6 * z2 ≤ 30 :=
                Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 6 * z2) (7 * z3)) (Nat.le_of_eq h)
              cases z2 with
              | zero =>
                -- z1 = 5, z2 = 0: 7 * z3 = 5
                have hD : 7 * z3 = 5 :=
                  add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 6 * Nat.zero) (7 * z3) 5 (Eq.trans h (rfl : (30:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 6 * Nat.zero + 5))
                rcases Nat.lt_or_ge z3 1 with hc | hc
                · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                      (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
                · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                      (Nat.le_of_eq hD)) (by decide)
              | succ z2k =>
                have hz2o : 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 6 * (z2k + 1) ≤ 30 :=
                  Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 6 * (z2k + 1)) (7 * z3)) (Nat.le_of_eq h)
                have hb : (1:Nat) ≤ (z2k + 1) := (Nat.le_add_left 1 z2k)
                have hfin : (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 6 * 1) ≤ 30 :=
                  Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hb) (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))))) hz2o
                exact absurd hfin (by decide)
            | succ z1123456 =>
              cases z1123456 with
              | zero =>
                -- z1 = 6
                have hz1 : 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))) + 6 * z2 ≤ 30 :=
                  Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))) + 6 * z2) (7 * z3)) (Nat.le_of_eq h)
                cases z2 with
                | zero =>
                  -- z1 = 6, z2 = 0: 7 * z3 = 0
                  have hD : 7 * z3 = 0 :=
                    add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))) + 6 * Nat.zero) (7 * z3) 0 (Eq.trans h (rfl : (30:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))) + 6 * Nat.zero + 0))
                  rcases Nat.lt_or_ge z3 1 with hc | hc
                  · exact Or.inr (Or.inr (Or.inr (⟨rfl, rfl, Nat.le_antisymm (Nat.le_of_lt_succ hc) (Nat.zero_le z3)⟩)))
                  · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                        (Nat.le_of_eq hD)) (by decide)
                | succ z2k =>
                  have hz2o : 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))) + 6 * (z2k + 1) ≤ 30 :=
                    Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))) + 6 * (z2k + 1)) (7 * z3)) (Nat.le_of_eq h)
                  have hb : (1:Nat) ≤ (z2k + 1) := (Nat.le_add_left 1 z2k)
                  have hfin : (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))) + 6 * 1) ≤ 30 :=
                    Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hb) (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))))) hz2o
                  exact absurd hfin (by decide)
              | succ z1123456k =>
                have hz1o : 5 * (((((((z1123456k + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 6 * z2 ≤ 30 :=
                  Nat.le_trans (Nat.le_add_right (5 * (((((((z1123456k + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 6 * z2) (7 * z3)) (Nat.le_of_eq h)
                have hb : (7:Nat) ≤ (((((((z1123456k + 1) + 1) + 1) + 1) + 1) + 1) + 1) := (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.le_add_left 1 z1123456k) 1) 1) 1) 1) 1) 1)
                have hfin : (5 * 7) ≤ 30 :=
                  Nat.le_trans (Nat.le_trans (Nat.mul_le_mul_left 5 hb) (Nat.le_add_right (5 * (((((((z1123456k + 1) + 1) + 1) + 1) + 1) + 1) + 1)) (6 * z2))) hz1o
                exact absurd hfin (by decide)

/-- `Z_(5,6,7)(35)` is exactly the listed set. -/
theorem Z567_35 : ∀ z1 z2 z3 : Nat,
    5 * z1 + 6 * z2 + 7 * z3 = 35 →
    (z1 = 0 ∧ z2 = 0 ∧ z3 = 5) ∨ (z1 = 1 ∧ z2 = 5 ∧ z3 = 0) ∨ (z1 = 2 ∧ z2 = 3 ∧ z3 = 1) ∨ (z1 = 3 ∧ z2 = 1 ∧ z3 = 2) ∨ (z1 = 7 ∧ z2 = 0 ∧ z3 = 0) := by
  intro z1 z2 z3 h
  have hz : 5 * z1 + 6 * z2 ≤ 35 :=
    Nat.le_trans (Nat.le_add_right (5 * z1 + 6 * z2) (7 * z3)) (Nat.le_of_eq h)
  cases z1 with
  | zero =>
    -- z1 = 0
    have hz1 : 5 * Nat.zero + 6 * z2 ≤ 35 :=
      Nat.le_trans (Nat.le_add_right (5 * Nat.zero + 6 * z2) (7 * z3)) (Nat.le_of_eq h)
    cases z2 with
    | zero =>
      -- z1 = 0, z2 = 0: 7 * z3 = 35
      have hD : 7 * z3 = 35 :=
        add_left_cancel_eq (5 * Nat.zero + 6 * Nat.zero) (7 * z3) 35 (Eq.trans h (rfl : (35:Nat) = 5 * Nat.zero + 6 * Nat.zero + 35))
      rcases Nat.lt_or_ge z3 6 with hc | hc
      · rcases Nat.lt_or_ge z3 5 with hc2 | hc2
        · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
              (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc2))) (by decide)
        · exact Or.inl (⟨rfl, rfl, Nat.le_antisymm (Nat.le_of_lt_succ hc) hc2⟩)
      · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
            (Nat.le_of_eq hD)) (by decide)
    | succ z21 =>
      cases z21 with
      | zero =>
        -- z1 = 0, z2 = 1: 7 * z3 = 29
        have hD : 7 * z3 = 29 :=
          add_left_cancel_eq (5 * Nat.zero + 6 * Nat.succ (Nat.zero)) (7 * z3) 29 (Eq.trans h (rfl : (35:Nat) = 5 * Nat.zero + 6 * Nat.succ (Nat.zero) + 29))
        rcases Nat.lt_or_ge z3 5 with hc | hc
        · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
              (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
        · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
              (Nat.le_of_eq hD)) (by decide)
      | succ z212 =>
        cases z212 with
        | zero =>
          -- z1 = 0, z2 = 2: 7 * z3 = 23
          have hD : 7 * z3 = 23 :=
            add_left_cancel_eq (5 * Nat.zero + 6 * Nat.succ (Nat.succ (Nat.zero))) (7 * z3) 23 (Eq.trans h (rfl : (35:Nat) = 5 * Nat.zero + 6 * Nat.succ (Nat.succ (Nat.zero)) + 23))
          rcases Nat.lt_or_ge z3 4 with hc | hc
          · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
          · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                (Nat.le_of_eq hD)) (by decide)
        | succ z2123 =>
          cases z2123 with
          | zero =>
            -- z1 = 0, z2 = 3: 7 * z3 = 17
            have hD : 7 * z3 = 17 :=
              add_left_cancel_eq (5 * Nat.zero + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) (7 * z3) 17 (Eq.trans h (rfl : (35:Nat) = 5 * Nat.zero + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 17))
            rcases Nat.lt_or_ge z3 3 with hc | hc
            · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                  (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
            · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                  (Nat.le_of_eq hD)) (by decide)
          | succ z21234 =>
            cases z21234 with
            | zero =>
              -- z1 = 0, z2 = 4: 7 * z3 = 11
              have hD : 7 * z3 = 11 :=
                add_left_cancel_eq (5 * Nat.zero + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) (7 * z3) 11 (Eq.trans h (rfl : (35:Nat) = 5 * Nat.zero + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 11))
              rcases Nat.lt_or_ge z3 2 with hc | hc
              · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                    (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
              · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                    (Nat.le_of_eq hD)) (by decide)
            | succ z212345 =>
              cases z212345 with
              | zero =>
                -- z1 = 0, z2 = 5: 7 * z3 = 5
                have hD : 7 * z3 = 5 :=
                  add_left_cancel_eq (5 * Nat.zero + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))) (7 * z3) 5 (Eq.trans h (rfl : (35:Nat) = 5 * Nat.zero + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 5))
                rcases Nat.lt_or_ge z3 1 with hc | hc
                · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                      (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
                · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                      (Nat.le_of_eq hD)) (by decide)
              | succ z212345k =>
                have hz2o : 5 * Nat.zero + 6 * ((((((z212345k + 1) + 1) + 1) + 1) + 1) + 1) ≤ 35 :=
                  Nat.le_trans (Nat.le_add_right (5 * Nat.zero + 6 * ((((((z212345k + 1) + 1) + 1) + 1) + 1) + 1)) (7 * z3)) (Nat.le_of_eq h)
                have hb : (6:Nat) ≤ ((((((z212345k + 1) + 1) + 1) + 1) + 1) + 1) := (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.le_add_left 1 z212345k) 1) 1) 1) 1) 1)
                have hfin : (5 * Nat.zero + 6 * 6) ≤ 35 :=
                  Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hb) (5 * Nat.zero)) hz2o
                exact absurd hfin (by decide)
  | succ z11 =>
    cases z11 with
    | zero =>
      -- z1 = 1
      have hz1 : 5 * Nat.succ (Nat.zero) + 6 * z2 ≤ 35 :=
        Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.zero) + 6 * z2) (7 * z3)) (Nat.le_of_eq h)
      cases z2 with
      | zero =>
        -- z1 = 1, z2 = 0: 7 * z3 = 30
        have hD : 7 * z3 = 30 :=
          add_left_cancel_eq (5 * Nat.succ (Nat.zero) + 6 * Nat.zero) (7 * z3) 30 (Eq.trans h (rfl : (35:Nat) = 5 * Nat.succ (Nat.zero) + 6 * Nat.zero + 30))
        rcases Nat.lt_or_ge z3 5 with hc | hc
        · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
              (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
        · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
              (Nat.le_of_eq hD)) (by decide)
      | succ z21 =>
        cases z21 with
        | zero =>
          -- z1 = 1, z2 = 1: 7 * z3 = 24
          have hD : 7 * z3 = 24 :=
            add_left_cancel_eq (5 * Nat.succ (Nat.zero) + 6 * Nat.succ (Nat.zero)) (7 * z3) 24 (Eq.trans h (rfl : (35:Nat) = 5 * Nat.succ (Nat.zero) + 6 * Nat.succ (Nat.zero) + 24))
          rcases Nat.lt_or_ge z3 4 with hc | hc
          · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
          · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                (Nat.le_of_eq hD)) (by decide)
        | succ z212 =>
          cases z212 with
          | zero =>
            -- z1 = 1, z2 = 2: 7 * z3 = 18
            have hD : 7 * z3 = 18 :=
              add_left_cancel_eq (5 * Nat.succ (Nat.zero) + 6 * Nat.succ (Nat.succ (Nat.zero))) (7 * z3) 18 (Eq.trans h (rfl : (35:Nat) = 5 * Nat.succ (Nat.zero) + 6 * Nat.succ (Nat.succ (Nat.zero)) + 18))
            rcases Nat.lt_or_ge z3 3 with hc | hc
            · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                  (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
            · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                  (Nat.le_of_eq hD)) (by decide)
          | succ z2123 =>
            cases z2123 with
            | zero =>
              -- z1 = 1, z2 = 3: 7 * z3 = 12
              have hD : 7 * z3 = 12 :=
                add_left_cancel_eq (5 * Nat.succ (Nat.zero) + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) (7 * z3) 12 (Eq.trans h (rfl : (35:Nat) = 5 * Nat.succ (Nat.zero) + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 12))
              rcases Nat.lt_or_ge z3 2 with hc | hc
              · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                    (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
              · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                    (Nat.le_of_eq hD)) (by decide)
            | succ z21234 =>
              cases z21234 with
              | zero =>
                -- z1 = 1, z2 = 4: 7 * z3 = 6
                have hD : 7 * z3 = 6 :=
                  add_left_cancel_eq (5 * Nat.succ (Nat.zero) + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) (7 * z3) 6 (Eq.trans h (rfl : (35:Nat) = 5 * Nat.succ (Nat.zero) + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6))
                rcases Nat.lt_or_ge z3 1 with hc | hc
                · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                      (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
                · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                      (Nat.le_of_eq hD)) (by decide)
              | succ z212345 =>
                cases z212345 with
                | zero =>
                  -- z1 = 1, z2 = 5: 7 * z3 = 0
                  have hD : 7 * z3 = 0 :=
                    add_left_cancel_eq (5 * Nat.succ (Nat.zero) + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))) (7 * z3) 0 (Eq.trans h (rfl : (35:Nat) = 5 * Nat.succ (Nat.zero) + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 0))
                  rcases Nat.lt_or_ge z3 1 with hc | hc
                  · exact Or.inr (Or.inl (⟨rfl, rfl, Nat.le_antisymm (Nat.le_of_lt_succ hc) (Nat.zero_le z3)⟩))
                  · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                        (Nat.le_of_eq hD)) (by decide)
                | succ z212345k =>
                  have hz2o : 5 * Nat.succ (Nat.zero) + 6 * ((((((z212345k + 1) + 1) + 1) + 1) + 1) + 1) ≤ 35 :=
                    Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.zero) + 6 * ((((((z212345k + 1) + 1) + 1) + 1) + 1) + 1)) (7 * z3)) (Nat.le_of_eq h)
                  have hb : (6:Nat) ≤ ((((((z212345k + 1) + 1) + 1) + 1) + 1) + 1) := (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.le_add_left 1 z212345k) 1) 1) 1) 1) 1)
                  have hfin : (5 * Nat.succ (Nat.zero) + 6 * 6) ≤ 35 :=
                    Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hb) (5 * Nat.succ (Nat.zero))) hz2o
                  exact absurd hfin (by decide)
    | succ z112 =>
      cases z112 with
      | zero =>
        -- z1 = 2
        have hz1 : 5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * z2 ≤ 35 :=
          Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * z2) (7 * z3)) (Nat.le_of_eq h)
        cases z2 with
        | zero =>
          -- z1 = 2, z2 = 0: 7 * z3 = 25
          have hD : 7 * z3 = 25 :=
            add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * Nat.zero) (7 * z3) 25 (Eq.trans h (rfl : (35:Nat) = 5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * Nat.zero + 25))
          rcases Nat.lt_or_ge z3 4 with hc | hc
          · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
          · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                (Nat.le_of_eq hD)) (by decide)
        | succ z21 =>
          cases z21 with
          | zero =>
            -- z1 = 2, z2 = 1: 7 * z3 = 19
            have hD : 7 * z3 = 19 :=
              add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * Nat.succ (Nat.zero)) (7 * z3) 19 (Eq.trans h (rfl : (35:Nat) = 5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * Nat.succ (Nat.zero) + 19))
            rcases Nat.lt_or_ge z3 3 with hc | hc
            · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                  (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
            · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                  (Nat.le_of_eq hD)) (by decide)
          | succ z212 =>
            cases z212 with
            | zero =>
              -- z1 = 2, z2 = 2: 7 * z3 = 13
              have hD : 7 * z3 = 13 :=
                add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * Nat.succ (Nat.succ (Nat.zero))) (7 * z3) 13 (Eq.trans h (rfl : (35:Nat) = 5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * Nat.succ (Nat.succ (Nat.zero)) + 13))
              rcases Nat.lt_or_ge z3 2 with hc | hc
              · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                    (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
              · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                    (Nat.le_of_eq hD)) (by decide)
            | succ z2123 =>
              cases z2123 with
              | zero =>
                -- z1 = 2, z2 = 3: 7 * z3 = 7
                have hD : 7 * z3 = 7 :=
                  add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) (7 * z3) 7 (Eq.trans h (rfl : (35:Nat) = 5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 7))
                rcases Nat.lt_or_ge z3 2 with hc | hc
                · rcases Nat.lt_or_ge z3 1 with hc2 | hc2
                  · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                        (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc2))) (by decide)
                  · exact Or.inr (Or.inr (Or.inl (⟨rfl, rfl, Nat.le_antisymm (Nat.le_of_lt_succ hc) hc2⟩)))
                · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                      (Nat.le_of_eq hD)) (by decide)
              | succ z21234 =>
                cases z21234 with
                | zero =>
                  -- z1 = 2, z2 = 4: 7 * z3 = 1
                  have hD : 7 * z3 = 1 :=
                    add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) (7 * z3) 1 (Eq.trans h (rfl : (35:Nat) = 5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 1))
                  rcases Nat.lt_or_ge z3 1 with hc | hc
                  · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                        (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
                  · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                        (Nat.le_of_eq hD)) (by decide)
                | succ z21234k =>
                  have hz2o : 5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * (((((z21234k + 1) + 1) + 1) + 1) + 1) ≤ 35 :=
                    Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * (((((z21234k + 1) + 1) + 1) + 1) + 1)) (7 * z3)) (Nat.le_of_eq h)
                  have hb : (5:Nat) ≤ (((((z21234k + 1) + 1) + 1) + 1) + 1) := (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.le_add_left 1 z21234k) 1) 1) 1) 1)
                  have hfin : (5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * 5) ≤ 35 :=
                    Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hb) (5 * Nat.succ (Nat.succ (Nat.zero)))) hz2o
                  exact absurd hfin (by decide)
      | succ z1123 =>
        cases z1123 with
        | zero =>
          -- z1 = 3
          have hz1 : 5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * z2 ≤ 35 :=
            Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * z2) (7 * z3)) (Nat.le_of_eq h)
          cases z2 with
          | zero =>
            -- z1 = 3, z2 = 0: 7 * z3 = 20
            have hD : 7 * z3 = 20 :=
              add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * Nat.zero) (7 * z3) 20 (Eq.trans h (rfl : (35:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * Nat.zero + 20))
            rcases Nat.lt_or_ge z3 3 with hc | hc
            · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                  (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
            · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                  (Nat.le_of_eq hD)) (by decide)
          | succ z21 =>
            cases z21 with
            | zero =>
              -- z1 = 3, z2 = 1: 7 * z3 = 14
              have hD : 7 * z3 = 14 :=
                add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * Nat.succ (Nat.zero)) (7 * z3) 14 (Eq.trans h (rfl : (35:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * Nat.succ (Nat.zero) + 14))
              rcases Nat.lt_or_ge z3 3 with hc | hc
              · rcases Nat.lt_or_ge z3 2 with hc2 | hc2
                · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                      (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc2))) (by decide)
                · exact Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, Nat.le_antisymm (Nat.le_of_lt_succ hc) hc2⟩))))
              · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                    (Nat.le_of_eq hD)) (by decide)
            | succ z212 =>
              cases z212 with
              | zero =>
                -- z1 = 3, z2 = 2: 7 * z3 = 8
                have hD : 7 * z3 = 8 :=
                  add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * Nat.succ (Nat.succ (Nat.zero))) (7 * z3) 8 (Eq.trans h (rfl : (35:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * Nat.succ (Nat.succ (Nat.zero)) + 8))
                rcases Nat.lt_or_ge z3 2 with hc | hc
                · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                      (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
                · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                      (Nat.le_of_eq hD)) (by decide)
              | succ z2123 =>
                cases z2123 with
                | zero =>
                  -- z1 = 3, z2 = 3: 7 * z3 = 2
                  have hD : 7 * z3 = 2 :=
                    add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) (7 * z3) 2 (Eq.trans h (rfl : (35:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 2))
                  rcases Nat.lt_or_ge z3 1 with hc | hc
                  · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                        (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
                  · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                        (Nat.le_of_eq hD)) (by decide)
                | succ z2123k =>
                  have hz2o : 5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * ((((z2123k + 1) + 1) + 1) + 1) ≤ 35 :=
                    Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * ((((z2123k + 1) + 1) + 1) + 1)) (7 * z3)) (Nat.le_of_eq h)
                  have hb : (4:Nat) ≤ ((((z2123k + 1) + 1) + 1) + 1) := (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.le_add_left 1 z2123k) 1) 1) 1)
                  have hfin : (5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * 4) ≤ 35 :=
                    Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hb) (5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) hz2o
                  exact absurd hfin (by decide)
        | succ z11234 =>
          cases z11234 with
          | zero =>
            -- z1 = 4
            have hz1 : 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * z2 ≤ 35 :=
              Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * z2) (7 * z3)) (Nat.le_of_eq h)
            cases z2 with
            | zero =>
              -- z1 = 4, z2 = 0: 7 * z3 = 15
              have hD : 7 * z3 = 15 :=
                add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * Nat.zero) (7 * z3) 15 (Eq.trans h (rfl : (35:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * Nat.zero + 15))
              rcases Nat.lt_or_ge z3 3 with hc | hc
              · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                    (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
              · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                    (Nat.le_of_eq hD)) (by decide)
            | succ z21 =>
              cases z21 with
              | zero =>
                -- z1 = 4, z2 = 1: 7 * z3 = 9
                have hD : 7 * z3 = 9 :=
                  add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * Nat.succ (Nat.zero)) (7 * z3) 9 (Eq.trans h (rfl : (35:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * Nat.succ (Nat.zero) + 9))
                rcases Nat.lt_or_ge z3 2 with hc | hc
                · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                      (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
                · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                      (Nat.le_of_eq hD)) (by decide)
              | succ z212 =>
                cases z212 with
                | zero =>
                  -- z1 = 4, z2 = 2: 7 * z3 = 3
                  have hD : 7 * z3 = 3 :=
                    add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * Nat.succ (Nat.succ (Nat.zero))) (7 * z3) 3 (Eq.trans h (rfl : (35:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * Nat.succ (Nat.succ (Nat.zero)) + 3))
                  rcases Nat.lt_or_ge z3 1 with hc | hc
                  · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                        (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
                  · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                        (Nat.le_of_eq hD)) (by decide)
                | succ z212k =>
                  have hz2o : 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * (((z212k + 1) + 1) + 1) ≤ 35 :=
                    Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * (((z212k + 1) + 1) + 1)) (7 * z3)) (Nat.le_of_eq h)
                  have hb : (3:Nat) ≤ (((z212k + 1) + 1) + 1) := (Nat.add_le_add_right (Nat.add_le_add_right (Nat.le_add_left 1 z212k) 1) 1)
                  have hfin : (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * 3) ≤ 35 :=
                    Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hb) (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))) hz2o
                  exact absurd hfin (by decide)
          | succ z112345 =>
            cases z112345 with
            | zero =>
              -- z1 = 5
              have hz1 : 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 6 * z2 ≤ 35 :=
                Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 6 * z2) (7 * z3)) (Nat.le_of_eq h)
              cases z2 with
              | zero =>
                -- z1 = 5, z2 = 0: 7 * z3 = 10
                have hD : 7 * z3 = 10 :=
                  add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 6 * Nat.zero) (7 * z3) 10 (Eq.trans h (rfl : (35:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 6 * Nat.zero + 10))
                rcases Nat.lt_or_ge z3 2 with hc | hc
                · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                      (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
                · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                      (Nat.le_of_eq hD)) (by decide)
              | succ z21 =>
                cases z21 with
                | zero =>
                  -- z1 = 5, z2 = 1: 7 * z3 = 4
                  have hD : 7 * z3 = 4 :=
                    add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 6 * Nat.succ (Nat.zero)) (7 * z3) 4 (Eq.trans h (rfl : (35:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 6 * Nat.succ (Nat.zero) + 4))
                  rcases Nat.lt_or_ge z3 1 with hc | hc
                  · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                        (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
                  · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                        (Nat.le_of_eq hD)) (by decide)
                | succ z21k =>
                  have hz2o : 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 6 * ((z21k + 1) + 1) ≤ 35 :=
                    Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 6 * ((z21k + 1) + 1)) (7 * z3)) (Nat.le_of_eq h)
                  have hb : (2:Nat) ≤ ((z21k + 1) + 1) := (Nat.add_le_add_right (Nat.le_add_left 1 z21k) 1)
                  have hfin : (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 6 * 2) ≤ 35 :=
                    Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hb) (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))))) hz2o
                  exact absurd hfin (by decide)
            | succ z1123456 =>
              cases z1123456 with
              | zero =>
                -- z1 = 6
                have hz1 : 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))) + 6 * z2 ≤ 35 :=
                  Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))) + 6 * z2) (7 * z3)) (Nat.le_of_eq h)
                cases z2 with
                | zero =>
                  -- z1 = 6, z2 = 0: 7 * z3 = 5
                  have hD : 7 * z3 = 5 :=
                    add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))) + 6 * Nat.zero) (7 * z3) 5 (Eq.trans h (rfl : (35:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))) + 6 * Nat.zero + 5))
                  rcases Nat.lt_or_ge z3 1 with hc | hc
                  · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                        (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
                  · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                        (Nat.le_of_eq hD)) (by decide)
                | succ z2k =>
                  have hz2o : 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))) + 6 * (z2k + 1) ≤ 35 :=
                    Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))) + 6 * (z2k + 1)) (7 * z3)) (Nat.le_of_eq h)
                  have hb : (1:Nat) ≤ (z2k + 1) := (Nat.le_add_left 1 z2k)
                  have hfin : (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))) + 6 * 1) ≤ 35 :=
                    Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hb) (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))))) hz2o
                  exact absurd hfin (by decide)
              | succ z11234567 =>
                cases z11234567 with
                | zero =>
                  -- z1 = 7
                  have hz1 : 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))))) + 6 * z2 ≤ 35 :=
                    Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))))) + 6 * z2) (7 * z3)) (Nat.le_of_eq h)
                  cases z2 with
                  | zero =>
                    -- z1 = 7, z2 = 0: 7 * z3 = 0
                    have hD : 7 * z3 = 0 :=
                      add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))))) + 6 * Nat.zero) (7 * z3) 0 (Eq.trans h (rfl : (35:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))))) + 6 * Nat.zero + 0))
                    rcases Nat.lt_or_ge z3 1 with hc | hc
                    · exact Or.inr (Or.inr (Or.inr (Or.inr (⟨rfl, rfl, Nat.le_antisymm (Nat.le_of_lt_succ hc) (Nat.zero_le z3)⟩))))
                    · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                          (Nat.le_of_eq hD)) (by decide)
                  | succ z2k =>
                    have hz2o : 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))))) + 6 * (z2k + 1) ≤ 35 :=
                      Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))))) + 6 * (z2k + 1)) (7 * z3)) (Nat.le_of_eq h)
                    have hb : (1:Nat) ≤ (z2k + 1) := (Nat.le_add_left 1 z2k)
                    have hfin : (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))))) + 6 * 1) ≤ 35 :=
                      Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hb) (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))))))) hz2o
                    exact absurd hfin (by decide)
                | succ z11234567k =>
                  have hz1o : 5 * ((((((((z11234567k + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 6 * z2 ≤ 35 :=
                    Nat.le_trans (Nat.le_add_right (5 * ((((((((z11234567k + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 6 * z2) (7 * z3)) (Nat.le_of_eq h)
                  have hb : (8:Nat) ≤ ((((((((z11234567k + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) := (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.le_add_left 1 z11234567k) 1) 1) 1) 1) 1) 1) 1)
                  have hfin : (5 * 8) ≤ 35 :=
                    Nat.le_trans (Nat.le_trans (Nat.mul_le_mul_left 5 hb) (Nat.le_add_right (5 * ((((((((z11234567k + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)) (6 * z2))) hz1o
                  exact absurd hfin (by decide)

/-- `Z_(5,6,7)(42)` is exactly the listed set. -/
theorem Z567_42 : ∀ z1 z2 z3 : Nat,
    5 * z1 + 6 * z2 + 7 * z3 = 42 →
    (z1 = 0 ∧ z2 = 0 ∧ z3 = 6) ∨ (z1 = 0 ∧ z2 = 7 ∧ z3 = 0) ∨ (z1 = 1 ∧ z2 = 5 ∧ z3 = 1) ∨ (z1 = 2 ∧ z2 = 3 ∧ z3 = 2) ∨ (z1 = 3 ∧ z2 = 1 ∧ z3 = 3) ∨ (z1 = 6 ∧ z2 = 2 ∧ z3 = 0) ∨ (z1 = 7 ∧ z2 = 0 ∧ z3 = 1) := by
  intro z1 z2 z3 h
  have hz : 5 * z1 + 6 * z2 ≤ 42 :=
    Nat.le_trans (Nat.le_add_right (5 * z1 + 6 * z2) (7 * z3)) (Nat.le_of_eq h)
  cases z1 with
  | zero =>
    -- z1 = 0
    have hz1 : 5 * Nat.zero + 6 * z2 ≤ 42 :=
      Nat.le_trans (Nat.le_add_right (5 * Nat.zero + 6 * z2) (7 * z3)) (Nat.le_of_eq h)
    cases z2 with
    | zero =>
      -- z1 = 0, z2 = 0: 7 * z3 = 42
      have hD : 7 * z3 = 42 :=
        add_left_cancel_eq (5 * Nat.zero + 6 * Nat.zero) (7 * z3) 42 (Eq.trans h (rfl : (42:Nat) = 5 * Nat.zero + 6 * Nat.zero + 42))
      rcases Nat.lt_or_ge z3 7 with hc | hc
      · rcases Nat.lt_or_ge z3 6 with hc2 | hc2
        · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
              (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc2))) (by decide)
        · exact Or.inl (⟨rfl, rfl, Nat.le_antisymm (Nat.le_of_lt_succ hc) hc2⟩)
      · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
            (Nat.le_of_eq hD)) (by decide)
    | succ z21 =>
      cases z21 with
      | zero =>
        -- z1 = 0, z2 = 1: 7 * z3 = 36
        have hD : 7 * z3 = 36 :=
          add_left_cancel_eq (5 * Nat.zero + 6 * Nat.succ (Nat.zero)) (7 * z3) 36 (Eq.trans h (rfl : (42:Nat) = 5 * Nat.zero + 6 * Nat.succ (Nat.zero) + 36))
        rcases Nat.lt_or_ge z3 6 with hc | hc
        · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
              (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
        · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
              (Nat.le_of_eq hD)) (by decide)
      | succ z212 =>
        cases z212 with
        | zero =>
          -- z1 = 0, z2 = 2: 7 * z3 = 30
          have hD : 7 * z3 = 30 :=
            add_left_cancel_eq (5 * Nat.zero + 6 * Nat.succ (Nat.succ (Nat.zero))) (7 * z3) 30 (Eq.trans h (rfl : (42:Nat) = 5 * Nat.zero + 6 * Nat.succ (Nat.succ (Nat.zero)) + 30))
          rcases Nat.lt_or_ge z3 5 with hc | hc
          · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
          · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                (Nat.le_of_eq hD)) (by decide)
        | succ z2123 =>
          cases z2123 with
          | zero =>
            -- z1 = 0, z2 = 3: 7 * z3 = 24
            have hD : 7 * z3 = 24 :=
              add_left_cancel_eq (5 * Nat.zero + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) (7 * z3) 24 (Eq.trans h (rfl : (42:Nat) = 5 * Nat.zero + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 24))
            rcases Nat.lt_or_ge z3 4 with hc | hc
            · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                  (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
            · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                  (Nat.le_of_eq hD)) (by decide)
          | succ z21234 =>
            cases z21234 with
            | zero =>
              -- z1 = 0, z2 = 4: 7 * z3 = 18
              have hD : 7 * z3 = 18 :=
                add_left_cancel_eq (5 * Nat.zero + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) (7 * z3) 18 (Eq.trans h (rfl : (42:Nat) = 5 * Nat.zero + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 18))
              rcases Nat.lt_or_ge z3 3 with hc | hc
              · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                    (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
              · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                    (Nat.le_of_eq hD)) (by decide)
            | succ z212345 =>
              cases z212345 with
              | zero =>
                -- z1 = 0, z2 = 5: 7 * z3 = 12
                have hD : 7 * z3 = 12 :=
                  add_left_cancel_eq (5 * Nat.zero + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))) (7 * z3) 12 (Eq.trans h (rfl : (42:Nat) = 5 * Nat.zero + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 12))
                rcases Nat.lt_or_ge z3 2 with hc | hc
                · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                      (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
                · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                      (Nat.le_of_eq hD)) (by decide)
              | succ z2123456 =>
                cases z2123456 with
                | zero =>
                  -- z1 = 0, z2 = 6: 7 * z3 = 6
                  have hD : 7 * z3 = 6 :=
                    add_left_cancel_eq (5 * Nat.zero + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))))) (7 * z3) 6 (Eq.trans h (rfl : (42:Nat) = 5 * Nat.zero + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))) + 6))
                  rcases Nat.lt_or_ge z3 1 with hc | hc
                  · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                        (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
                  · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                        (Nat.le_of_eq hD)) (by decide)
                | succ z21234567 =>
                  cases z21234567 with
                  | zero =>
                    -- z1 = 0, z2 = 7: 7 * z3 = 0
                    have hD : 7 * z3 = 0 :=
                      add_left_cancel_eq (5 * Nat.zero + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))))) (7 * z3) 0 (Eq.trans h (rfl : (42:Nat) = 5 * Nat.zero + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))))) + 0))
                    rcases Nat.lt_or_ge z3 1 with hc | hc
                    · exact Or.inr (Or.inl (⟨rfl, rfl, Nat.le_antisymm (Nat.le_of_lt_succ hc) (Nat.zero_le z3)⟩))
                    · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                          (Nat.le_of_eq hD)) (by decide)
                  | succ z21234567k =>
                    have hz2o : 5 * Nat.zero + 6 * ((((((((z21234567k + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) ≤ 42 :=
                      Nat.le_trans (Nat.le_add_right (5 * Nat.zero + 6 * ((((((((z21234567k + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)) (7 * z3)) (Nat.le_of_eq h)
                    have hb : (8:Nat) ≤ ((((((((z21234567k + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) := (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.le_add_left 1 z21234567k) 1) 1) 1) 1) 1) 1) 1)
                    have hfin : (5 * Nat.zero + 6 * 8) ≤ 42 :=
                      Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hb) (5 * Nat.zero)) hz2o
                    exact absurd hfin (by decide)
  | succ z11 =>
    cases z11 with
    | zero =>
      -- z1 = 1
      have hz1 : 5 * Nat.succ (Nat.zero) + 6 * z2 ≤ 42 :=
        Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.zero) + 6 * z2) (7 * z3)) (Nat.le_of_eq h)
      cases z2 with
      | zero =>
        -- z1 = 1, z2 = 0: 7 * z3 = 37
        have hD : 7 * z3 = 37 :=
          add_left_cancel_eq (5 * Nat.succ (Nat.zero) + 6 * Nat.zero) (7 * z3) 37 (Eq.trans h (rfl : (42:Nat) = 5 * Nat.succ (Nat.zero) + 6 * Nat.zero + 37))
        rcases Nat.lt_or_ge z3 6 with hc | hc
        · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
              (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
        · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
              (Nat.le_of_eq hD)) (by decide)
      | succ z21 =>
        cases z21 with
        | zero =>
          -- z1 = 1, z2 = 1: 7 * z3 = 31
          have hD : 7 * z3 = 31 :=
            add_left_cancel_eq (5 * Nat.succ (Nat.zero) + 6 * Nat.succ (Nat.zero)) (7 * z3) 31 (Eq.trans h (rfl : (42:Nat) = 5 * Nat.succ (Nat.zero) + 6 * Nat.succ (Nat.zero) + 31))
          rcases Nat.lt_or_ge z3 5 with hc | hc
          · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
          · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                (Nat.le_of_eq hD)) (by decide)
        | succ z212 =>
          cases z212 with
          | zero =>
            -- z1 = 1, z2 = 2: 7 * z3 = 25
            have hD : 7 * z3 = 25 :=
              add_left_cancel_eq (5 * Nat.succ (Nat.zero) + 6 * Nat.succ (Nat.succ (Nat.zero))) (7 * z3) 25 (Eq.trans h (rfl : (42:Nat) = 5 * Nat.succ (Nat.zero) + 6 * Nat.succ (Nat.succ (Nat.zero)) + 25))
            rcases Nat.lt_or_ge z3 4 with hc | hc
            · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                  (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
            · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                  (Nat.le_of_eq hD)) (by decide)
          | succ z2123 =>
            cases z2123 with
            | zero =>
              -- z1 = 1, z2 = 3: 7 * z3 = 19
              have hD : 7 * z3 = 19 :=
                add_left_cancel_eq (5 * Nat.succ (Nat.zero) + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) (7 * z3) 19 (Eq.trans h (rfl : (42:Nat) = 5 * Nat.succ (Nat.zero) + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 19))
              rcases Nat.lt_or_ge z3 3 with hc | hc
              · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                    (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
              · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                    (Nat.le_of_eq hD)) (by decide)
            | succ z21234 =>
              cases z21234 with
              | zero =>
                -- z1 = 1, z2 = 4: 7 * z3 = 13
                have hD : 7 * z3 = 13 :=
                  add_left_cancel_eq (5 * Nat.succ (Nat.zero) + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) (7 * z3) 13 (Eq.trans h (rfl : (42:Nat) = 5 * Nat.succ (Nat.zero) + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 13))
                rcases Nat.lt_or_ge z3 2 with hc | hc
                · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                      (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
                · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                      (Nat.le_of_eq hD)) (by decide)
              | succ z212345 =>
                cases z212345 with
                | zero =>
                  -- z1 = 1, z2 = 5: 7 * z3 = 7
                  have hD : 7 * z3 = 7 :=
                    add_left_cancel_eq (5 * Nat.succ (Nat.zero) + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))) (7 * z3) 7 (Eq.trans h (rfl : (42:Nat) = 5 * Nat.succ (Nat.zero) + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 7))
                  rcases Nat.lt_or_ge z3 2 with hc | hc
                  · rcases Nat.lt_or_ge z3 1 with hc2 | hc2
                    · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                          (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc2))) (by decide)
                    · exact Or.inr (Or.inr (Or.inl (⟨rfl, rfl, Nat.le_antisymm (Nat.le_of_lt_succ hc) hc2⟩)))
                  · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                        (Nat.le_of_eq hD)) (by decide)
                | succ z2123456 =>
                  cases z2123456 with
                  | zero =>
                    -- z1 = 1, z2 = 6: 7 * z3 = 1
                    have hD : 7 * z3 = 1 :=
                      add_left_cancel_eq (5 * Nat.succ (Nat.zero) + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))))) (7 * z3) 1 (Eq.trans h (rfl : (42:Nat) = 5 * Nat.succ (Nat.zero) + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))) + 1))
                    rcases Nat.lt_or_ge z3 1 with hc | hc
                    · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                          (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
                    · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                          (Nat.le_of_eq hD)) (by decide)
                  | succ z2123456k =>
                    have hz2o : 5 * Nat.succ (Nat.zero) + 6 * (((((((z2123456k + 1) + 1) + 1) + 1) + 1) + 1) + 1) ≤ 42 :=
                      Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.zero) + 6 * (((((((z2123456k + 1) + 1) + 1) + 1) + 1) + 1) + 1)) (7 * z3)) (Nat.le_of_eq h)
                    have hb : (7:Nat) ≤ (((((((z2123456k + 1) + 1) + 1) + 1) + 1) + 1) + 1) := (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.le_add_left 1 z2123456k) 1) 1) 1) 1) 1) 1)
                    have hfin : (5 * Nat.succ (Nat.zero) + 6 * 7) ≤ 42 :=
                      Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hb) (5 * Nat.succ (Nat.zero))) hz2o
                    exact absurd hfin (by decide)
    | succ z112 =>
      cases z112 with
      | zero =>
        -- z1 = 2
        have hz1 : 5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * z2 ≤ 42 :=
          Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * z2) (7 * z3)) (Nat.le_of_eq h)
        cases z2 with
        | zero =>
          -- z1 = 2, z2 = 0: 7 * z3 = 32
          have hD : 7 * z3 = 32 :=
            add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * Nat.zero) (7 * z3) 32 (Eq.trans h (rfl : (42:Nat) = 5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * Nat.zero + 32))
          rcases Nat.lt_or_ge z3 5 with hc | hc
          · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
          · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                (Nat.le_of_eq hD)) (by decide)
        | succ z21 =>
          cases z21 with
          | zero =>
            -- z1 = 2, z2 = 1: 7 * z3 = 26
            have hD : 7 * z3 = 26 :=
              add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * Nat.succ (Nat.zero)) (7 * z3) 26 (Eq.trans h (rfl : (42:Nat) = 5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * Nat.succ (Nat.zero) + 26))
            rcases Nat.lt_or_ge z3 4 with hc | hc
            · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                  (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
            · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                  (Nat.le_of_eq hD)) (by decide)
          | succ z212 =>
            cases z212 with
            | zero =>
              -- z1 = 2, z2 = 2: 7 * z3 = 20
              have hD : 7 * z3 = 20 :=
                add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * Nat.succ (Nat.succ (Nat.zero))) (7 * z3) 20 (Eq.trans h (rfl : (42:Nat) = 5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * Nat.succ (Nat.succ (Nat.zero)) + 20))
              rcases Nat.lt_or_ge z3 3 with hc | hc
              · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                    (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
              · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                    (Nat.le_of_eq hD)) (by decide)
            | succ z2123 =>
              cases z2123 with
              | zero =>
                -- z1 = 2, z2 = 3: 7 * z3 = 14
                have hD : 7 * z3 = 14 :=
                  add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) (7 * z3) 14 (Eq.trans h (rfl : (42:Nat) = 5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 14))
                rcases Nat.lt_or_ge z3 3 with hc | hc
                · rcases Nat.lt_or_ge z3 2 with hc2 | hc2
                  · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                        (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc2))) (by decide)
                  · exact Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, Nat.le_antisymm (Nat.le_of_lt_succ hc) hc2⟩))))
                · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                      (Nat.le_of_eq hD)) (by decide)
              | succ z21234 =>
                cases z21234 with
                | zero =>
                  -- z1 = 2, z2 = 4: 7 * z3 = 8
                  have hD : 7 * z3 = 8 :=
                    add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) (7 * z3) 8 (Eq.trans h (rfl : (42:Nat) = 5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 8))
                  rcases Nat.lt_or_ge z3 2 with hc | hc
                  · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                        (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
                  · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                        (Nat.le_of_eq hD)) (by decide)
                | succ z212345 =>
                  cases z212345 with
                  | zero =>
                    -- z1 = 2, z2 = 5: 7 * z3 = 2
                    have hD : 7 * z3 = 2 :=
                      add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))) (7 * z3) 2 (Eq.trans h (rfl : (42:Nat) = 5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 2))
                    rcases Nat.lt_or_ge z3 1 with hc | hc
                    · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                          (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
                    · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                          (Nat.le_of_eq hD)) (by decide)
                  | succ z212345k =>
                    have hz2o : 5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * ((((((z212345k + 1) + 1) + 1) + 1) + 1) + 1) ≤ 42 :=
                      Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * ((((((z212345k + 1) + 1) + 1) + 1) + 1) + 1)) (7 * z3)) (Nat.le_of_eq h)
                    have hb : (6:Nat) ≤ ((((((z212345k + 1) + 1) + 1) + 1) + 1) + 1) := (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.le_add_left 1 z212345k) 1) 1) 1) 1) 1)
                    have hfin : (5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * 6) ≤ 42 :=
                      Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hb) (5 * Nat.succ (Nat.succ (Nat.zero)))) hz2o
                    exact absurd hfin (by decide)
      | succ z1123 =>
        cases z1123 with
        | zero =>
          -- z1 = 3
          have hz1 : 5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * z2 ≤ 42 :=
            Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * z2) (7 * z3)) (Nat.le_of_eq h)
          cases z2 with
          | zero =>
            -- z1 = 3, z2 = 0: 7 * z3 = 27
            have hD : 7 * z3 = 27 :=
              add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * Nat.zero) (7 * z3) 27 (Eq.trans h (rfl : (42:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * Nat.zero + 27))
            rcases Nat.lt_or_ge z3 4 with hc | hc
            · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                  (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
            · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                  (Nat.le_of_eq hD)) (by decide)
          | succ z21 =>
            cases z21 with
            | zero =>
              -- z1 = 3, z2 = 1: 7 * z3 = 21
              have hD : 7 * z3 = 21 :=
                add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * Nat.succ (Nat.zero)) (7 * z3) 21 (Eq.trans h (rfl : (42:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * Nat.succ (Nat.zero) + 21))
              rcases Nat.lt_or_ge z3 4 with hc | hc
              · rcases Nat.lt_or_ge z3 3 with hc2 | hc2
                · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                      (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc2))) (by decide)
                · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, Nat.le_antisymm (Nat.le_of_lt_succ hc) hc2⟩)))))
              · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                    (Nat.le_of_eq hD)) (by decide)
            | succ z212 =>
              cases z212 with
              | zero =>
                -- z1 = 3, z2 = 2: 7 * z3 = 15
                have hD : 7 * z3 = 15 :=
                  add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * Nat.succ (Nat.succ (Nat.zero))) (7 * z3) 15 (Eq.trans h (rfl : (42:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * Nat.succ (Nat.succ (Nat.zero)) + 15))
                rcases Nat.lt_or_ge z3 3 with hc | hc
                · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                      (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
                · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                      (Nat.le_of_eq hD)) (by decide)
              | succ z2123 =>
                cases z2123 with
                | zero =>
                  -- z1 = 3, z2 = 3: 7 * z3 = 9
                  have hD : 7 * z3 = 9 :=
                    add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) (7 * z3) 9 (Eq.trans h (rfl : (42:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 9))
                  rcases Nat.lt_or_ge z3 2 with hc | hc
                  · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                        (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
                  · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                        (Nat.le_of_eq hD)) (by decide)
                | succ z21234 =>
                  cases z21234 with
                  | zero =>
                    -- z1 = 3, z2 = 4: 7 * z3 = 3
                    have hD : 7 * z3 = 3 :=
                      add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) (7 * z3) 3 (Eq.trans h (rfl : (42:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 3))
                    rcases Nat.lt_or_ge z3 1 with hc | hc
                    · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                          (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
                    · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                          (Nat.le_of_eq hD)) (by decide)
                  | succ z21234k =>
                    have hz2o : 5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * (((((z21234k + 1) + 1) + 1) + 1) + 1) ≤ 42 :=
                      Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * (((((z21234k + 1) + 1) + 1) + 1) + 1)) (7 * z3)) (Nat.le_of_eq h)
                    have hb : (5:Nat) ≤ (((((z21234k + 1) + 1) + 1) + 1) + 1) := (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.le_add_left 1 z21234k) 1) 1) 1) 1)
                    have hfin : (5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * 5) ≤ 42 :=
                      Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hb) (5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) hz2o
                    exact absurd hfin (by decide)
        | succ z11234 =>
          cases z11234 with
          | zero =>
            -- z1 = 4
            have hz1 : 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * z2 ≤ 42 :=
              Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * z2) (7 * z3)) (Nat.le_of_eq h)
            cases z2 with
            | zero =>
              -- z1 = 4, z2 = 0: 7 * z3 = 22
              have hD : 7 * z3 = 22 :=
                add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * Nat.zero) (7 * z3) 22 (Eq.trans h (rfl : (42:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * Nat.zero + 22))
              rcases Nat.lt_or_ge z3 4 with hc | hc
              · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                    (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
              · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                    (Nat.le_of_eq hD)) (by decide)
            | succ z21 =>
              cases z21 with
              | zero =>
                -- z1 = 4, z2 = 1: 7 * z3 = 16
                have hD : 7 * z3 = 16 :=
                  add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * Nat.succ (Nat.zero)) (7 * z3) 16 (Eq.trans h (rfl : (42:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * Nat.succ (Nat.zero) + 16))
                rcases Nat.lt_or_ge z3 3 with hc | hc
                · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                      (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
                · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                      (Nat.le_of_eq hD)) (by decide)
              | succ z212 =>
                cases z212 with
                | zero =>
                  -- z1 = 4, z2 = 2: 7 * z3 = 10
                  have hD : 7 * z3 = 10 :=
                    add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * Nat.succ (Nat.succ (Nat.zero))) (7 * z3) 10 (Eq.trans h (rfl : (42:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * Nat.succ (Nat.succ (Nat.zero)) + 10))
                  rcases Nat.lt_or_ge z3 2 with hc | hc
                  · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                        (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
                  · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                        (Nat.le_of_eq hD)) (by decide)
                | succ z2123 =>
                  cases z2123 with
                  | zero =>
                    -- z1 = 4, z2 = 3: 7 * z3 = 4
                    have hD : 7 * z3 = 4 :=
                      add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) (7 * z3) 4 (Eq.trans h (rfl : (42:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 4))
                    rcases Nat.lt_or_ge z3 1 with hc | hc
                    · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                          (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
                    · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                          (Nat.le_of_eq hD)) (by decide)
                  | succ z2123k =>
                    have hz2o : 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * ((((z2123k + 1) + 1) + 1) + 1) ≤ 42 :=
                      Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * ((((z2123k + 1) + 1) + 1) + 1)) (7 * z3)) (Nat.le_of_eq h)
                    have hb : (4:Nat) ≤ ((((z2123k + 1) + 1) + 1) + 1) := (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.le_add_left 1 z2123k) 1) 1) 1)
                    have hfin : (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * 4) ≤ 42 :=
                      Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hb) (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))) hz2o
                    exact absurd hfin (by decide)
          | succ z112345 =>
            cases z112345 with
            | zero =>
              -- z1 = 5
              have hz1 : 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 6 * z2 ≤ 42 :=
                Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 6 * z2) (7 * z3)) (Nat.le_of_eq h)
              cases z2 with
              | zero =>
                -- z1 = 5, z2 = 0: 7 * z3 = 17
                have hD : 7 * z3 = 17 :=
                  add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 6 * Nat.zero) (7 * z3) 17 (Eq.trans h (rfl : (42:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 6 * Nat.zero + 17))
                rcases Nat.lt_or_ge z3 3 with hc | hc
                · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                      (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
                · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                      (Nat.le_of_eq hD)) (by decide)
              | succ z21 =>
                cases z21 with
                | zero =>
                  -- z1 = 5, z2 = 1: 7 * z3 = 11
                  have hD : 7 * z3 = 11 :=
                    add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 6 * Nat.succ (Nat.zero)) (7 * z3) 11 (Eq.trans h (rfl : (42:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 6 * Nat.succ (Nat.zero) + 11))
                  rcases Nat.lt_or_ge z3 2 with hc | hc
                  · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                        (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
                  · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                        (Nat.le_of_eq hD)) (by decide)
                | succ z212 =>
                  cases z212 with
                  | zero =>
                    -- z1 = 5, z2 = 2: 7 * z3 = 5
                    have hD : 7 * z3 = 5 :=
                      add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 6 * Nat.succ (Nat.succ (Nat.zero))) (7 * z3) 5 (Eq.trans h (rfl : (42:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 6 * Nat.succ (Nat.succ (Nat.zero)) + 5))
                    rcases Nat.lt_or_ge z3 1 with hc | hc
                    · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                          (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
                    · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                          (Nat.le_of_eq hD)) (by decide)
                  | succ z212k =>
                    have hz2o : 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 6 * (((z212k + 1) + 1) + 1) ≤ 42 :=
                      Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 6 * (((z212k + 1) + 1) + 1)) (7 * z3)) (Nat.le_of_eq h)
                    have hb : (3:Nat) ≤ (((z212k + 1) + 1) + 1) := (Nat.add_le_add_right (Nat.add_le_add_right (Nat.le_add_left 1 z212k) 1) 1)
                    have hfin : (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 6 * 3) ≤ 42 :=
                      Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hb) (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))))) hz2o
                    exact absurd hfin (by decide)
            | succ z1123456 =>
              cases z1123456 with
              | zero =>
                -- z1 = 6
                have hz1 : 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))) + 6 * z2 ≤ 42 :=
                  Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))) + 6 * z2) (7 * z3)) (Nat.le_of_eq h)
                cases z2 with
                | zero =>
                  -- z1 = 6, z2 = 0: 7 * z3 = 12
                  have hD : 7 * z3 = 12 :=
                    add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))) + 6 * Nat.zero) (7 * z3) 12 (Eq.trans h (rfl : (42:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))) + 6 * Nat.zero + 12))
                  rcases Nat.lt_or_ge z3 2 with hc | hc
                  · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                        (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
                  · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                        (Nat.le_of_eq hD)) (by decide)
                | succ z21 =>
                  cases z21 with
                  | zero =>
                    -- z1 = 6, z2 = 1: 7 * z3 = 6
                    have hD : 7 * z3 = 6 :=
                      add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))) + 6 * Nat.succ (Nat.zero)) (7 * z3) 6 (Eq.trans h (rfl : (42:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))) + 6 * Nat.succ (Nat.zero) + 6))
                    rcases Nat.lt_or_ge z3 1 with hc | hc
                    · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                          (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
                    · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                          (Nat.le_of_eq hD)) (by decide)
                  | succ z212 =>
                    cases z212 with
                    | zero =>
                      -- z1 = 6, z2 = 2: 7 * z3 = 0
                      have hD : 7 * z3 = 0 :=
                        add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))) + 6 * Nat.succ (Nat.succ (Nat.zero))) (7 * z3) 0 (Eq.trans h (rfl : (42:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))) + 6 * Nat.succ (Nat.succ (Nat.zero)) + 0))
                      rcases Nat.lt_or_ge z3 1 with hc | hc
                      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, rfl, Nat.le_antisymm (Nat.le_of_lt_succ hc) (Nat.zero_le z3)⟩))))))
                      · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                            (Nat.le_of_eq hD)) (by decide)
                    | succ z212k =>
                      have hz2o : 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))) + 6 * (((z212k + 1) + 1) + 1) ≤ 42 :=
                        Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))) + 6 * (((z212k + 1) + 1) + 1)) (7 * z3)) (Nat.le_of_eq h)
                      have hb : (3:Nat) ≤ (((z212k + 1) + 1) + 1) := (Nat.add_le_add_right (Nat.add_le_add_right (Nat.le_add_left 1 z212k) 1) 1)
                      have hfin : (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))) + 6 * 3) ≤ 42 :=
                        Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hb) (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))))) hz2o
                      exact absurd hfin (by decide)
              | succ z11234567 =>
                cases z11234567 with
                | zero =>
                  -- z1 = 7
                  have hz1 : 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))))) + 6 * z2 ≤ 42 :=
                    Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))))) + 6 * z2) (7 * z3)) (Nat.le_of_eq h)
                  cases z2 with
                  | zero =>
                    -- z1 = 7, z2 = 0: 7 * z3 = 7
                    have hD : 7 * z3 = 7 :=
                      add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))))) + 6 * Nat.zero) (7 * z3) 7 (Eq.trans h (rfl : (42:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))))) + 6 * Nat.zero + 7))
                    rcases Nat.lt_or_ge z3 2 with hc | hc
                    · rcases Nat.lt_or_ge z3 1 with hc2 | hc2
                      · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                            (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc2))) (by decide)
                      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨rfl, rfl, Nat.le_antisymm (Nat.le_of_lt_succ hc) hc2⟩))))))
                    · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                          (Nat.le_of_eq hD)) (by decide)
                  | succ z21 =>
                    cases z21 with
                    | zero =>
                      -- z1 = 7, z2 = 1: 7 * z3 = 1
                      have hD : 7 * z3 = 1 :=
                        add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))))) + 6 * Nat.succ (Nat.zero)) (7 * z3) 1 (Eq.trans h (rfl : (42:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))))) + 6 * Nat.succ (Nat.zero) + 1))
                      rcases Nat.lt_or_ge z3 1 with hc | hc
                      · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                            (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
                      · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                            (Nat.le_of_eq hD)) (by decide)
                    | succ z21k =>
                      have hz2o : 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))))) + 6 * ((z21k + 1) + 1) ≤ 42 :=
                        Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))))) + 6 * ((z21k + 1) + 1)) (7 * z3)) (Nat.le_of_eq h)
                      have hb : (2:Nat) ≤ ((z21k + 1) + 1) := (Nat.add_le_add_right (Nat.le_add_left 1 z21k) 1)
                      have hfin : (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))))) + 6 * 2) ≤ 42 :=
                        Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hb) (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))))))) hz2o
                      exact absurd hfin (by decide)
                | succ z112345678 =>
                  cases z112345678 with
                  | zero =>
                    -- z1 = 8
                    have hz1 : 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))))) + 6 * z2 ≤ 42 :=
                      Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))))) + 6 * z2) (7 * z3)) (Nat.le_of_eq h)
                    cases z2 with
                    | zero =>
                      -- z1 = 8, z2 = 0: 7 * z3 = 2
                      have hD : 7 * z3 = 2 :=
                        add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))))) + 6 * Nat.zero) (7 * z3) 2 (Eq.trans h (rfl : (42:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))))) + 6 * Nat.zero + 2))
                      rcases Nat.lt_or_ge z3 1 with hc | hc
                      · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                            (Nat.mul_le_mul_left 7 (Nat.le_of_lt_succ hc))) (by decide)
                      · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 7 hc)
                            (Nat.le_of_eq hD)) (by decide)
                    | succ z2k =>
                      have hz2o : 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))))) + 6 * (z2k + 1) ≤ 42 :=
                        Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))))) + 6 * (z2k + 1)) (7 * z3)) (Nat.le_of_eq h)
                      have hb : (1:Nat) ≤ (z2k + 1) := (Nat.le_add_left 1 z2k)
                      have hfin : (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))))) + 6 * 1) ≤ 42 :=
                        Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hb) (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))))))) hz2o
                      exact absurd hfin (by decide)
                  | succ z112345678k =>
                    have hz1o : 5 * (((((((((z112345678k + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 6 * z2 ≤ 42 :=
                      Nat.le_trans (Nat.le_add_right (5 * (((((((((z112345678k + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 6 * z2) (7 * z3)) (Nat.le_of_eq h)
                    have hb : (9:Nat) ≤ (((((((((z112345678k + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) := (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.le_add_left 1 z112345678k) 1) 1) 1) 1) 1) 1) 1) 1)
                    have hfin : (5 * 9) ≤ 42 :=
                      Nat.le_trans (Nat.le_trans (Nat.mul_le_mul_left 5 hb) (Nat.le_add_right (5 * (((((((((z112345678k + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)) (6 * z2))) hz1o
                    exact absurd hfin (by decide)

/-- `Z_(5,6,25)(25)` is exactly the listed set. -/
theorem Z5625_25 : ∀ z1 z2 z3 : Nat,
    5 * z1 + 6 * z2 + 25 * z3 = 25 →
    (z1 = 0 ∧ z2 = 0 ∧ z3 = 1) ∨ (z1 = 5 ∧ z2 = 0 ∧ z3 = 0) := by
  intro z1 z2 z3 h
  have hz : 5 * z1 + 6 * z2 ≤ 25 :=
    Nat.le_trans (Nat.le_add_right (5 * z1 + 6 * z2) (25 * z3)) (Nat.le_of_eq h)
  cases z1 with
  | zero =>
    -- z1 = 0
    have hz1 : 5 * Nat.zero + 6 * z2 ≤ 25 :=
      Nat.le_trans (Nat.le_add_right (5 * Nat.zero + 6 * z2) (25 * z3)) (Nat.le_of_eq h)
    cases z2 with
    | zero =>
      -- z1 = 0, z2 = 0: 25 * z3 = 25
      have hD : 25 * z3 = 25 :=
        add_left_cancel_eq (5 * Nat.zero + 6 * Nat.zero) (25 * z3) 25 (Eq.trans h (rfl : (25:Nat) = 5 * Nat.zero + 6 * Nat.zero + 25))
      rcases Nat.lt_or_ge z3 2 with hc | hc
      · rcases Nat.lt_or_ge z3 1 with hc2 | hc2
        · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
              (Nat.mul_le_mul_left 25 (Nat.le_of_lt_succ hc2))) (by decide)
        · exact Or.inl (⟨rfl, rfl, Nat.le_antisymm (Nat.le_of_lt_succ hc) hc2⟩)
      · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 25 hc)
            (Nat.le_of_eq hD)) (by decide)
    | succ z21 =>
      cases z21 with
      | zero =>
        -- z1 = 0, z2 = 1: 25 * z3 = 19
        have hD : 25 * z3 = 19 :=
          add_left_cancel_eq (5 * Nat.zero + 6 * Nat.succ (Nat.zero)) (25 * z3) 19 (Eq.trans h (rfl : (25:Nat) = 5 * Nat.zero + 6 * Nat.succ (Nat.zero) + 19))
        rcases Nat.lt_or_ge z3 1 with hc | hc
        · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
              (Nat.mul_le_mul_left 25 (Nat.le_of_lt_succ hc))) (by decide)
        · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 25 hc)
              (Nat.le_of_eq hD)) (by decide)
      | succ z212 =>
        cases z212 with
        | zero =>
          -- z1 = 0, z2 = 2: 25 * z3 = 13
          have hD : 25 * z3 = 13 :=
            add_left_cancel_eq (5 * Nat.zero + 6 * Nat.succ (Nat.succ (Nat.zero))) (25 * z3) 13 (Eq.trans h (rfl : (25:Nat) = 5 * Nat.zero + 6 * Nat.succ (Nat.succ (Nat.zero)) + 13))
          rcases Nat.lt_or_ge z3 1 with hc | hc
          · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                (Nat.mul_le_mul_left 25 (Nat.le_of_lt_succ hc))) (by decide)
          · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 25 hc)
                (Nat.le_of_eq hD)) (by decide)
        | succ z2123 =>
          cases z2123 with
          | zero =>
            -- z1 = 0, z2 = 3: 25 * z3 = 7
            have hD : 25 * z3 = 7 :=
              add_left_cancel_eq (5 * Nat.zero + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) (25 * z3) 7 (Eq.trans h (rfl : (25:Nat) = 5 * Nat.zero + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 7))
            rcases Nat.lt_or_ge z3 1 with hc | hc
            · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                  (Nat.mul_le_mul_left 25 (Nat.le_of_lt_succ hc))) (by decide)
            · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 25 hc)
                  (Nat.le_of_eq hD)) (by decide)
          | succ z21234 =>
            cases z21234 with
            | zero =>
              -- z1 = 0, z2 = 4: 25 * z3 = 1
              have hD : 25 * z3 = 1 :=
                add_left_cancel_eq (5 * Nat.zero + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) (25 * z3) 1 (Eq.trans h (rfl : (25:Nat) = 5 * Nat.zero + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 1))
              rcases Nat.lt_or_ge z3 1 with hc | hc
              · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                    (Nat.mul_le_mul_left 25 (Nat.le_of_lt_succ hc))) (by decide)
              · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 25 hc)
                    (Nat.le_of_eq hD)) (by decide)
            | succ z21234k =>
              have hz2o : 5 * Nat.zero + 6 * (((((z21234k + 1) + 1) + 1) + 1) + 1) ≤ 25 :=
                Nat.le_trans (Nat.le_add_right (5 * Nat.zero + 6 * (((((z21234k + 1) + 1) + 1) + 1) + 1)) (25 * z3)) (Nat.le_of_eq h)
              have hb : (5:Nat) ≤ (((((z21234k + 1) + 1) + 1) + 1) + 1) := (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.le_add_left 1 z21234k) 1) 1) 1) 1)
              have hfin : (5 * Nat.zero + 6 * 5) ≤ 25 :=
                Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hb) (5 * Nat.zero)) hz2o
              exact absurd hfin (by decide)
  | succ z11 =>
    cases z11 with
    | zero =>
      -- z1 = 1
      have hz1 : 5 * Nat.succ (Nat.zero) + 6 * z2 ≤ 25 :=
        Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.zero) + 6 * z2) (25 * z3)) (Nat.le_of_eq h)
      cases z2 with
      | zero =>
        -- z1 = 1, z2 = 0: 25 * z3 = 20
        have hD : 25 * z3 = 20 :=
          add_left_cancel_eq (5 * Nat.succ (Nat.zero) + 6 * Nat.zero) (25 * z3) 20 (Eq.trans h (rfl : (25:Nat) = 5 * Nat.succ (Nat.zero) + 6 * Nat.zero + 20))
        rcases Nat.lt_or_ge z3 1 with hc | hc
        · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
              (Nat.mul_le_mul_left 25 (Nat.le_of_lt_succ hc))) (by decide)
        · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 25 hc)
              (Nat.le_of_eq hD)) (by decide)
      | succ z21 =>
        cases z21 with
        | zero =>
          -- z1 = 1, z2 = 1: 25 * z3 = 14
          have hD : 25 * z3 = 14 :=
            add_left_cancel_eq (5 * Nat.succ (Nat.zero) + 6 * Nat.succ (Nat.zero)) (25 * z3) 14 (Eq.trans h (rfl : (25:Nat) = 5 * Nat.succ (Nat.zero) + 6 * Nat.succ (Nat.zero) + 14))
          rcases Nat.lt_or_ge z3 1 with hc | hc
          · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                (Nat.mul_le_mul_left 25 (Nat.le_of_lt_succ hc))) (by decide)
          · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 25 hc)
                (Nat.le_of_eq hD)) (by decide)
        | succ z212 =>
          cases z212 with
          | zero =>
            -- z1 = 1, z2 = 2: 25 * z3 = 8
            have hD : 25 * z3 = 8 :=
              add_left_cancel_eq (5 * Nat.succ (Nat.zero) + 6 * Nat.succ (Nat.succ (Nat.zero))) (25 * z3) 8 (Eq.trans h (rfl : (25:Nat) = 5 * Nat.succ (Nat.zero) + 6 * Nat.succ (Nat.succ (Nat.zero)) + 8))
            rcases Nat.lt_or_ge z3 1 with hc | hc
            · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                  (Nat.mul_le_mul_left 25 (Nat.le_of_lt_succ hc))) (by decide)
            · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 25 hc)
                  (Nat.le_of_eq hD)) (by decide)
          | succ z2123 =>
            cases z2123 with
            | zero =>
              -- z1 = 1, z2 = 3: 25 * z3 = 2
              have hD : 25 * z3 = 2 :=
                add_left_cancel_eq (5 * Nat.succ (Nat.zero) + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) (25 * z3) 2 (Eq.trans h (rfl : (25:Nat) = 5 * Nat.succ (Nat.zero) + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 2))
              rcases Nat.lt_or_ge z3 1 with hc | hc
              · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                    (Nat.mul_le_mul_left 25 (Nat.le_of_lt_succ hc))) (by decide)
              · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 25 hc)
                    (Nat.le_of_eq hD)) (by decide)
            | succ z2123k =>
              have hz2o : 5 * Nat.succ (Nat.zero) + 6 * ((((z2123k + 1) + 1) + 1) + 1) ≤ 25 :=
                Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.zero) + 6 * ((((z2123k + 1) + 1) + 1) + 1)) (25 * z3)) (Nat.le_of_eq h)
              have hb : (4:Nat) ≤ ((((z2123k + 1) + 1) + 1) + 1) := (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.le_add_left 1 z2123k) 1) 1) 1)
              have hfin : (5 * Nat.succ (Nat.zero) + 6 * 4) ≤ 25 :=
                Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hb) (5 * Nat.succ (Nat.zero))) hz2o
              exact absurd hfin (by decide)
    | succ z112 =>
      cases z112 with
      | zero =>
        -- z1 = 2
        have hz1 : 5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * z2 ≤ 25 :=
          Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * z2) (25 * z3)) (Nat.le_of_eq h)
        cases z2 with
        | zero =>
          -- z1 = 2, z2 = 0: 25 * z3 = 15
          have hD : 25 * z3 = 15 :=
            add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * Nat.zero) (25 * z3) 15 (Eq.trans h (rfl : (25:Nat) = 5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * Nat.zero + 15))
          rcases Nat.lt_or_ge z3 1 with hc | hc
          · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                (Nat.mul_le_mul_left 25 (Nat.le_of_lt_succ hc))) (by decide)
          · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 25 hc)
                (Nat.le_of_eq hD)) (by decide)
        | succ z21 =>
          cases z21 with
          | zero =>
            -- z1 = 2, z2 = 1: 25 * z3 = 9
            have hD : 25 * z3 = 9 :=
              add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * Nat.succ (Nat.zero)) (25 * z3) 9 (Eq.trans h (rfl : (25:Nat) = 5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * Nat.succ (Nat.zero) + 9))
            rcases Nat.lt_or_ge z3 1 with hc | hc
            · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                  (Nat.mul_le_mul_left 25 (Nat.le_of_lt_succ hc))) (by decide)
            · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 25 hc)
                  (Nat.le_of_eq hD)) (by decide)
          | succ z212 =>
            cases z212 with
            | zero =>
              -- z1 = 2, z2 = 2: 25 * z3 = 3
              have hD : 25 * z3 = 3 :=
                add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * Nat.succ (Nat.succ (Nat.zero))) (25 * z3) 3 (Eq.trans h (rfl : (25:Nat) = 5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * Nat.succ (Nat.succ (Nat.zero)) + 3))
              rcases Nat.lt_or_ge z3 1 with hc | hc
              · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                    (Nat.mul_le_mul_left 25 (Nat.le_of_lt_succ hc))) (by decide)
              · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 25 hc)
                    (Nat.le_of_eq hD)) (by decide)
            | succ z212k =>
              have hz2o : 5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * (((z212k + 1) + 1) + 1) ≤ 25 :=
                Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * (((z212k + 1) + 1) + 1)) (25 * z3)) (Nat.le_of_eq h)
              have hb : (3:Nat) ≤ (((z212k + 1) + 1) + 1) := (Nat.add_le_add_right (Nat.add_le_add_right (Nat.le_add_left 1 z212k) 1) 1)
              have hfin : (5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * 3) ≤ 25 :=
                Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hb) (5 * Nat.succ (Nat.succ (Nat.zero)))) hz2o
              exact absurd hfin (by decide)
      | succ z1123 =>
        cases z1123 with
        | zero =>
          -- z1 = 3
          have hz1 : 5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * z2 ≤ 25 :=
            Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * z2) (25 * z3)) (Nat.le_of_eq h)
          cases z2 with
          | zero =>
            -- z1 = 3, z2 = 0: 25 * z3 = 10
            have hD : 25 * z3 = 10 :=
              add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * Nat.zero) (25 * z3) 10 (Eq.trans h (rfl : (25:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * Nat.zero + 10))
            rcases Nat.lt_or_ge z3 1 with hc | hc
            · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                  (Nat.mul_le_mul_left 25 (Nat.le_of_lt_succ hc))) (by decide)
            · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 25 hc)
                  (Nat.le_of_eq hD)) (by decide)
          | succ z21 =>
            cases z21 with
            | zero =>
              -- z1 = 3, z2 = 1: 25 * z3 = 4
              have hD : 25 * z3 = 4 :=
                add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * Nat.succ (Nat.zero)) (25 * z3) 4 (Eq.trans h (rfl : (25:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * Nat.succ (Nat.zero) + 4))
              rcases Nat.lt_or_ge z3 1 with hc | hc
              · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                    (Nat.mul_le_mul_left 25 (Nat.le_of_lt_succ hc))) (by decide)
              · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 25 hc)
                    (Nat.le_of_eq hD)) (by decide)
            | succ z21k =>
              have hz2o : 5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * ((z21k + 1) + 1) ≤ 25 :=
                Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * ((z21k + 1) + 1)) (25 * z3)) (Nat.le_of_eq h)
              have hb : (2:Nat) ≤ ((z21k + 1) + 1) := (Nat.add_le_add_right (Nat.le_add_left 1 z21k) 1)
              have hfin : (5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * 2) ≤ 25 :=
                Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hb) (5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) hz2o
              exact absurd hfin (by decide)
        | succ z11234 =>
          cases z11234 with
          | zero =>
            -- z1 = 4
            have hz1 : 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * z2 ≤ 25 :=
              Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * z2) (25 * z3)) (Nat.le_of_eq h)
            cases z2 with
            | zero =>
              -- z1 = 4, z2 = 0: 25 * z3 = 5
              have hD : 25 * z3 = 5 :=
                add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * Nat.zero) (25 * z3) 5 (Eq.trans h (rfl : (25:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * Nat.zero + 5))
              rcases Nat.lt_or_ge z3 1 with hc | hc
              · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                    (Nat.mul_le_mul_left 25 (Nat.le_of_lt_succ hc))) (by decide)
              · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 25 hc)
                    (Nat.le_of_eq hD)) (by decide)
            | succ z2k =>
              have hz2o : 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * (z2k + 1) ≤ 25 :=
                Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * (z2k + 1)) (25 * z3)) (Nat.le_of_eq h)
              have hb : (1:Nat) ≤ (z2k + 1) := (Nat.le_add_left 1 z2k)
              have hfin : (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * 1) ≤ 25 :=
                Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hb) (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))) hz2o
              exact absurd hfin (by decide)
          | succ z112345 =>
            cases z112345 with
            | zero =>
              -- z1 = 5
              have hz1 : 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 6 * z2 ≤ 25 :=
                Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 6 * z2) (25 * z3)) (Nat.le_of_eq h)
              cases z2 with
              | zero =>
                -- z1 = 5, z2 = 0: 25 * z3 = 0
                have hD : 25 * z3 = 0 :=
                  add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 6 * Nat.zero) (25 * z3) 0 (Eq.trans h (rfl : (25:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 6 * Nat.zero + 0))
                rcases Nat.lt_or_ge z3 1 with hc | hc
                · exact Or.inr (⟨rfl, rfl, Nat.le_antisymm (Nat.le_of_lt_succ hc) (Nat.zero_le z3)⟩)
                · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 25 hc)
                      (Nat.le_of_eq hD)) (by decide)
              | succ z2k =>
                have hz2o : 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 6 * (z2k + 1) ≤ 25 :=
                  Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 6 * (z2k + 1)) (25 * z3)) (Nat.le_of_eq h)
                have hb : (1:Nat) ≤ (z2k + 1) := (Nat.le_add_left 1 z2k)
                have hfin : (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 6 * 1) ≤ 25 :=
                  Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hb) (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))))) hz2o
                exact absurd hfin (by decide)
            | succ z112345k =>
              have hz1o : 5 * ((((((z112345k + 1) + 1) + 1) + 1) + 1) + 1) + 6 * z2 ≤ 25 :=
                Nat.le_trans (Nat.le_add_right (5 * ((((((z112345k + 1) + 1) + 1) + 1) + 1) + 1) + 6 * z2) (25 * z3)) (Nat.le_of_eq h)
              have hb : (6:Nat) ≤ ((((((z112345k + 1) + 1) + 1) + 1) + 1) + 1) := (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.le_add_left 1 z112345k) 1) 1) 1) 1) 1)
              have hfin : (5 * 6) ≤ 25 :=
                Nat.le_trans (Nat.le_trans (Nat.mul_le_mul_left 5 hb) (Nat.le_add_right (5 * ((((((z112345k + 1) + 1) + 1) + 1) + 1) + 1)) (6 * z2))) hz1o
              exact absurd hfin (by decide)

/-- `Z_(5,6,25)(30)` is exactly the listed set. -/
theorem Z5625_30 : ∀ z1 z2 z3 : Nat,
    5 * z1 + 6 * z2 + 25 * z3 = 30 →
    (z1 = 0 ∧ z2 = 5 ∧ z3 = 0) ∨ (z1 = 1 ∧ z2 = 0 ∧ z3 = 1) ∨ (z1 = 6 ∧ z2 = 0 ∧ z3 = 0) := by
  intro z1 z2 z3 h
  have hz : 5 * z1 + 6 * z2 ≤ 30 :=
    Nat.le_trans (Nat.le_add_right (5 * z1 + 6 * z2) (25 * z3)) (Nat.le_of_eq h)
  cases z1 with
  | zero =>
    -- z1 = 0
    have hz1 : 5 * Nat.zero + 6 * z2 ≤ 30 :=
      Nat.le_trans (Nat.le_add_right (5 * Nat.zero + 6 * z2) (25 * z3)) (Nat.le_of_eq h)
    cases z2 with
    | zero =>
      -- z1 = 0, z2 = 0: 25 * z3 = 30
      have hD : 25 * z3 = 30 :=
        add_left_cancel_eq (5 * Nat.zero + 6 * Nat.zero) (25 * z3) 30 (Eq.trans h (rfl : (30:Nat) = 5 * Nat.zero + 6 * Nat.zero + 30))
      rcases Nat.lt_or_ge z3 2 with hc | hc
      · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
            (Nat.mul_le_mul_left 25 (Nat.le_of_lt_succ hc))) (by decide)
      · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 25 hc)
            (Nat.le_of_eq hD)) (by decide)
    | succ z21 =>
      cases z21 with
      | zero =>
        -- z1 = 0, z2 = 1: 25 * z3 = 24
        have hD : 25 * z3 = 24 :=
          add_left_cancel_eq (5 * Nat.zero + 6 * Nat.succ (Nat.zero)) (25 * z3) 24 (Eq.trans h (rfl : (30:Nat) = 5 * Nat.zero + 6 * Nat.succ (Nat.zero) + 24))
        rcases Nat.lt_or_ge z3 1 with hc | hc
        · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
              (Nat.mul_le_mul_left 25 (Nat.le_of_lt_succ hc))) (by decide)
        · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 25 hc)
              (Nat.le_of_eq hD)) (by decide)
      | succ z212 =>
        cases z212 with
        | zero =>
          -- z1 = 0, z2 = 2: 25 * z3 = 18
          have hD : 25 * z3 = 18 :=
            add_left_cancel_eq (5 * Nat.zero + 6 * Nat.succ (Nat.succ (Nat.zero))) (25 * z3) 18 (Eq.trans h (rfl : (30:Nat) = 5 * Nat.zero + 6 * Nat.succ (Nat.succ (Nat.zero)) + 18))
          rcases Nat.lt_or_ge z3 1 with hc | hc
          · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                (Nat.mul_le_mul_left 25 (Nat.le_of_lt_succ hc))) (by decide)
          · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 25 hc)
                (Nat.le_of_eq hD)) (by decide)
        | succ z2123 =>
          cases z2123 with
          | zero =>
            -- z1 = 0, z2 = 3: 25 * z3 = 12
            have hD : 25 * z3 = 12 :=
              add_left_cancel_eq (5 * Nat.zero + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) (25 * z3) 12 (Eq.trans h (rfl : (30:Nat) = 5 * Nat.zero + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 12))
            rcases Nat.lt_or_ge z3 1 with hc | hc
            · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                  (Nat.mul_le_mul_left 25 (Nat.le_of_lt_succ hc))) (by decide)
            · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 25 hc)
                  (Nat.le_of_eq hD)) (by decide)
          | succ z21234 =>
            cases z21234 with
            | zero =>
              -- z1 = 0, z2 = 4: 25 * z3 = 6
              have hD : 25 * z3 = 6 :=
                add_left_cancel_eq (5 * Nat.zero + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) (25 * z3) 6 (Eq.trans h (rfl : (30:Nat) = 5 * Nat.zero + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6))
              rcases Nat.lt_or_ge z3 1 with hc | hc
              · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                    (Nat.mul_le_mul_left 25 (Nat.le_of_lt_succ hc))) (by decide)
              · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 25 hc)
                    (Nat.le_of_eq hD)) (by decide)
            | succ z212345 =>
              cases z212345 with
              | zero =>
                -- z1 = 0, z2 = 5: 25 * z3 = 0
                have hD : 25 * z3 = 0 :=
                  add_left_cancel_eq (5 * Nat.zero + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))) (25 * z3) 0 (Eq.trans h (rfl : (30:Nat) = 5 * Nat.zero + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 0))
                rcases Nat.lt_or_ge z3 1 with hc | hc
                · exact Or.inl (⟨rfl, rfl, Nat.le_antisymm (Nat.le_of_lt_succ hc) (Nat.zero_le z3)⟩)
                · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 25 hc)
                      (Nat.le_of_eq hD)) (by decide)
              | succ z212345k =>
                have hz2o : 5 * Nat.zero + 6 * ((((((z212345k + 1) + 1) + 1) + 1) + 1) + 1) ≤ 30 :=
                  Nat.le_trans (Nat.le_add_right (5 * Nat.zero + 6 * ((((((z212345k + 1) + 1) + 1) + 1) + 1) + 1)) (25 * z3)) (Nat.le_of_eq h)
                have hb : (6:Nat) ≤ ((((((z212345k + 1) + 1) + 1) + 1) + 1) + 1) := (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.le_add_left 1 z212345k) 1) 1) 1) 1) 1)
                have hfin : (5 * Nat.zero + 6 * 6) ≤ 30 :=
                  Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hb) (5 * Nat.zero)) hz2o
                exact absurd hfin (by decide)
  | succ z11 =>
    cases z11 with
    | zero =>
      -- z1 = 1
      have hz1 : 5 * Nat.succ (Nat.zero) + 6 * z2 ≤ 30 :=
        Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.zero) + 6 * z2) (25 * z3)) (Nat.le_of_eq h)
      cases z2 with
      | zero =>
        -- z1 = 1, z2 = 0: 25 * z3 = 25
        have hD : 25 * z3 = 25 :=
          add_left_cancel_eq (5 * Nat.succ (Nat.zero) + 6 * Nat.zero) (25 * z3) 25 (Eq.trans h (rfl : (30:Nat) = 5 * Nat.succ (Nat.zero) + 6 * Nat.zero + 25))
        rcases Nat.lt_or_ge z3 2 with hc | hc
        · rcases Nat.lt_or_ge z3 1 with hc2 | hc2
          · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                (Nat.mul_le_mul_left 25 (Nat.le_of_lt_succ hc2))) (by decide)
          · exact Or.inr (Or.inl (⟨rfl, rfl, Nat.le_antisymm (Nat.le_of_lt_succ hc) hc2⟩))
        · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 25 hc)
              (Nat.le_of_eq hD)) (by decide)
      | succ z21 =>
        cases z21 with
        | zero =>
          -- z1 = 1, z2 = 1: 25 * z3 = 19
          have hD : 25 * z3 = 19 :=
            add_left_cancel_eq (5 * Nat.succ (Nat.zero) + 6 * Nat.succ (Nat.zero)) (25 * z3) 19 (Eq.trans h (rfl : (30:Nat) = 5 * Nat.succ (Nat.zero) + 6 * Nat.succ (Nat.zero) + 19))
          rcases Nat.lt_or_ge z3 1 with hc | hc
          · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                (Nat.mul_le_mul_left 25 (Nat.le_of_lt_succ hc))) (by decide)
          · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 25 hc)
                (Nat.le_of_eq hD)) (by decide)
        | succ z212 =>
          cases z212 with
          | zero =>
            -- z1 = 1, z2 = 2: 25 * z3 = 13
            have hD : 25 * z3 = 13 :=
              add_left_cancel_eq (5 * Nat.succ (Nat.zero) + 6 * Nat.succ (Nat.succ (Nat.zero))) (25 * z3) 13 (Eq.trans h (rfl : (30:Nat) = 5 * Nat.succ (Nat.zero) + 6 * Nat.succ (Nat.succ (Nat.zero)) + 13))
            rcases Nat.lt_or_ge z3 1 with hc | hc
            · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                  (Nat.mul_le_mul_left 25 (Nat.le_of_lt_succ hc))) (by decide)
            · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 25 hc)
                  (Nat.le_of_eq hD)) (by decide)
          | succ z2123 =>
            cases z2123 with
            | zero =>
              -- z1 = 1, z2 = 3: 25 * z3 = 7
              have hD : 25 * z3 = 7 :=
                add_left_cancel_eq (5 * Nat.succ (Nat.zero) + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) (25 * z3) 7 (Eq.trans h (rfl : (30:Nat) = 5 * Nat.succ (Nat.zero) + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 7))
              rcases Nat.lt_or_ge z3 1 with hc | hc
              · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                    (Nat.mul_le_mul_left 25 (Nat.le_of_lt_succ hc))) (by decide)
              · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 25 hc)
                    (Nat.le_of_eq hD)) (by decide)
            | succ z21234 =>
              cases z21234 with
              | zero =>
                -- z1 = 1, z2 = 4: 25 * z3 = 1
                have hD : 25 * z3 = 1 :=
                  add_left_cancel_eq (5 * Nat.succ (Nat.zero) + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) (25 * z3) 1 (Eq.trans h (rfl : (30:Nat) = 5 * Nat.succ (Nat.zero) + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 1))
                rcases Nat.lt_or_ge z3 1 with hc | hc
                · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                      (Nat.mul_le_mul_left 25 (Nat.le_of_lt_succ hc))) (by decide)
                · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 25 hc)
                      (Nat.le_of_eq hD)) (by decide)
              | succ z21234k =>
                have hz2o : 5 * Nat.succ (Nat.zero) + 6 * (((((z21234k + 1) + 1) + 1) + 1) + 1) ≤ 30 :=
                  Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.zero) + 6 * (((((z21234k + 1) + 1) + 1) + 1) + 1)) (25 * z3)) (Nat.le_of_eq h)
                have hb : (5:Nat) ≤ (((((z21234k + 1) + 1) + 1) + 1) + 1) := (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.le_add_left 1 z21234k) 1) 1) 1) 1)
                have hfin : (5 * Nat.succ (Nat.zero) + 6 * 5) ≤ 30 :=
                  Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hb) (5 * Nat.succ (Nat.zero))) hz2o
                exact absurd hfin (by decide)
    | succ z112 =>
      cases z112 with
      | zero =>
        -- z1 = 2
        have hz1 : 5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * z2 ≤ 30 :=
          Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * z2) (25 * z3)) (Nat.le_of_eq h)
        cases z2 with
        | zero =>
          -- z1 = 2, z2 = 0: 25 * z3 = 20
          have hD : 25 * z3 = 20 :=
            add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * Nat.zero) (25 * z3) 20 (Eq.trans h (rfl : (30:Nat) = 5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * Nat.zero + 20))
          rcases Nat.lt_or_ge z3 1 with hc | hc
          · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                (Nat.mul_le_mul_left 25 (Nat.le_of_lt_succ hc))) (by decide)
          · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 25 hc)
                (Nat.le_of_eq hD)) (by decide)
        | succ z21 =>
          cases z21 with
          | zero =>
            -- z1 = 2, z2 = 1: 25 * z3 = 14
            have hD : 25 * z3 = 14 :=
              add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * Nat.succ (Nat.zero)) (25 * z3) 14 (Eq.trans h (rfl : (30:Nat) = 5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * Nat.succ (Nat.zero) + 14))
            rcases Nat.lt_or_ge z3 1 with hc | hc
            · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                  (Nat.mul_le_mul_left 25 (Nat.le_of_lt_succ hc))) (by decide)
            · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 25 hc)
                  (Nat.le_of_eq hD)) (by decide)
          | succ z212 =>
            cases z212 with
            | zero =>
              -- z1 = 2, z2 = 2: 25 * z3 = 8
              have hD : 25 * z3 = 8 :=
                add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * Nat.succ (Nat.succ (Nat.zero))) (25 * z3) 8 (Eq.trans h (rfl : (30:Nat) = 5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * Nat.succ (Nat.succ (Nat.zero)) + 8))
              rcases Nat.lt_or_ge z3 1 with hc | hc
              · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                    (Nat.mul_le_mul_left 25 (Nat.le_of_lt_succ hc))) (by decide)
              · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 25 hc)
                    (Nat.le_of_eq hD)) (by decide)
            | succ z2123 =>
              cases z2123 with
              | zero =>
                -- z1 = 2, z2 = 3: 25 * z3 = 2
                have hD : 25 * z3 = 2 :=
                  add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) (25 * z3) 2 (Eq.trans h (rfl : (30:Nat) = 5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 2))
                rcases Nat.lt_or_ge z3 1 with hc | hc
                · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                      (Nat.mul_le_mul_left 25 (Nat.le_of_lt_succ hc))) (by decide)
                · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 25 hc)
                      (Nat.le_of_eq hD)) (by decide)
              | succ z2123k =>
                have hz2o : 5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * ((((z2123k + 1) + 1) + 1) + 1) ≤ 30 :=
                  Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * ((((z2123k + 1) + 1) + 1) + 1)) (25 * z3)) (Nat.le_of_eq h)
                have hb : (4:Nat) ≤ ((((z2123k + 1) + 1) + 1) + 1) := (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.le_add_left 1 z2123k) 1) 1) 1)
                have hfin : (5 * Nat.succ (Nat.succ (Nat.zero)) + 6 * 4) ≤ 30 :=
                  Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hb) (5 * Nat.succ (Nat.succ (Nat.zero)))) hz2o
                exact absurd hfin (by decide)
      | succ z1123 =>
        cases z1123 with
        | zero =>
          -- z1 = 3
          have hz1 : 5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * z2 ≤ 30 :=
            Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * z2) (25 * z3)) (Nat.le_of_eq h)
          cases z2 with
          | zero =>
            -- z1 = 3, z2 = 0: 25 * z3 = 15
            have hD : 25 * z3 = 15 :=
              add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * Nat.zero) (25 * z3) 15 (Eq.trans h (rfl : (30:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * Nat.zero + 15))
            rcases Nat.lt_or_ge z3 1 with hc | hc
            · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                  (Nat.mul_le_mul_left 25 (Nat.le_of_lt_succ hc))) (by decide)
            · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 25 hc)
                  (Nat.le_of_eq hD)) (by decide)
          | succ z21 =>
            cases z21 with
            | zero =>
              -- z1 = 3, z2 = 1: 25 * z3 = 9
              have hD : 25 * z3 = 9 :=
                add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * Nat.succ (Nat.zero)) (25 * z3) 9 (Eq.trans h (rfl : (30:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * Nat.succ (Nat.zero) + 9))
              rcases Nat.lt_or_ge z3 1 with hc | hc
              · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                    (Nat.mul_le_mul_left 25 (Nat.le_of_lt_succ hc))) (by decide)
              · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 25 hc)
                    (Nat.le_of_eq hD)) (by decide)
            | succ z212 =>
              cases z212 with
              | zero =>
                -- z1 = 3, z2 = 2: 25 * z3 = 3
                have hD : 25 * z3 = 3 :=
                  add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * Nat.succ (Nat.succ (Nat.zero))) (25 * z3) 3 (Eq.trans h (rfl : (30:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * Nat.succ (Nat.succ (Nat.zero)) + 3))
                rcases Nat.lt_or_ge z3 1 with hc | hc
                · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                      (Nat.mul_le_mul_left 25 (Nat.le_of_lt_succ hc))) (by decide)
                · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 25 hc)
                      (Nat.le_of_eq hD)) (by decide)
              | succ z212k =>
                have hz2o : 5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * (((z212k + 1) + 1) + 1) ≤ 30 :=
                  Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * (((z212k + 1) + 1) + 1)) (25 * z3)) (Nat.le_of_eq h)
                have hb : (3:Nat) ≤ (((z212k + 1) + 1) + 1) := (Nat.add_le_add_right (Nat.add_le_add_right (Nat.le_add_left 1 z212k) 1) 1)
                have hfin : (5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))) + 6 * 3) ≤ 30 :=
                  Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hb) (5 * Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) hz2o
                exact absurd hfin (by decide)
        | succ z11234 =>
          cases z11234 with
          | zero =>
            -- z1 = 4
            have hz1 : 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * z2 ≤ 30 :=
              Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * z2) (25 * z3)) (Nat.le_of_eq h)
            cases z2 with
            | zero =>
              -- z1 = 4, z2 = 0: 25 * z3 = 10
              have hD : 25 * z3 = 10 :=
                add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * Nat.zero) (25 * z3) 10 (Eq.trans h (rfl : (30:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * Nat.zero + 10))
              rcases Nat.lt_or_ge z3 1 with hc | hc
              · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                    (Nat.mul_le_mul_left 25 (Nat.le_of_lt_succ hc))) (by decide)
              · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 25 hc)
                    (Nat.le_of_eq hD)) (by decide)
            | succ z21 =>
              cases z21 with
              | zero =>
                -- z1 = 4, z2 = 1: 25 * z3 = 4
                have hD : 25 * z3 = 4 :=
                  add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * Nat.succ (Nat.zero)) (25 * z3) 4 (Eq.trans h (rfl : (30:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * Nat.succ (Nat.zero) + 4))
                rcases Nat.lt_or_ge z3 1 with hc | hc
                · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                      (Nat.mul_le_mul_left 25 (Nat.le_of_lt_succ hc))) (by decide)
                · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 25 hc)
                      (Nat.le_of_eq hD)) (by decide)
              | succ z21k =>
                have hz2o : 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * ((z21k + 1) + 1) ≤ 30 :=
                  Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * ((z21k + 1) + 1)) (25 * z3)) (Nat.le_of_eq h)
                have hb : (2:Nat) ≤ ((z21k + 1) + 1) := (Nat.add_le_add_right (Nat.le_add_left 1 z21k) 1)
                have hfin : (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))) + 6 * 2) ≤ 30 :=
                  Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hb) (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))) hz2o
                exact absurd hfin (by decide)
          | succ z112345 =>
            cases z112345 with
            | zero =>
              -- z1 = 5
              have hz1 : 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 6 * z2 ≤ 30 :=
                Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 6 * z2) (25 * z3)) (Nat.le_of_eq h)
              cases z2 with
              | zero =>
                -- z1 = 5, z2 = 0: 25 * z3 = 5
                have hD : 25 * z3 = 5 :=
                  add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 6 * Nat.zero) (25 * z3) 5 (Eq.trans h (rfl : (30:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 6 * Nat.zero + 5))
                rcases Nat.lt_or_ge z3 1 with hc | hc
                · exact absurd (Nat.le_trans (Nat.le_of_eq hD.symm)
                      (Nat.mul_le_mul_left 25 (Nat.le_of_lt_succ hc))) (by decide)
                · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 25 hc)
                      (Nat.le_of_eq hD)) (by decide)
              | succ z2k =>
                have hz2o : 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 6 * (z2k + 1) ≤ 30 :=
                  Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 6 * (z2k + 1)) (25 * z3)) (Nat.le_of_eq h)
                have hb : (1:Nat) ≤ (z2k + 1) := (Nat.le_add_left 1 z2k)
                have hfin : (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))) + 6 * 1) ≤ 30 :=
                  Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hb) (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero))))))) hz2o
                exact absurd hfin (by decide)
            | succ z1123456 =>
              cases z1123456 with
              | zero =>
                -- z1 = 6
                have hz1 : 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))) + 6 * z2 ≤ 30 :=
                  Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))) + 6 * z2) (25 * z3)) (Nat.le_of_eq h)
                cases z2 with
                | zero =>
                  -- z1 = 6, z2 = 0: 25 * z3 = 0
                  have hD : 25 * z3 = 0 :=
                    add_left_cancel_eq (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))) + 6 * Nat.zero) (25 * z3) 0 (Eq.trans h (rfl : (30:Nat) = 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))) + 6 * Nat.zero + 0))
                  rcases Nat.lt_or_ge z3 1 with hc | hc
                  · exact Or.inr (Or.inr (⟨rfl, rfl, Nat.le_antisymm (Nat.le_of_lt_succ hc) (Nat.zero_le z3)⟩))
                  · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 25 hc)
                        (Nat.le_of_eq hD)) (by decide)
                | succ z2k =>
                  have hz2o : 5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))) + 6 * (z2k + 1) ≤ 30 :=
                    Nat.le_trans (Nat.le_add_right (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))) + 6 * (z2k + 1)) (25 * z3)) (Nat.le_of_eq h)
                  have hb : (1:Nat) ≤ (z2k + 1) := (Nat.le_add_left 1 z2k)
                  have hfin : (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))) + 6 * 1) ≤ 30 :=
                    Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hb) (5 * Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.zero)))))))) hz2o
                  exact absurd hfin (by decide)
              | succ z1123456k =>
                have hz1o : 5 * (((((((z1123456k + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 6 * z2 ≤ 30 :=
                  Nat.le_trans (Nat.le_add_right (5 * (((((((z1123456k + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 6 * z2) (25 * z3)) (Nat.le_of_eq h)
                have hb : (7:Nat) ≤ (((((((z1123456k + 1) + 1) + 1) + 1) + 1) + 1) + 1) := (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Nat.le_add_left 1 z1123456k) 1) 1) 1) 1) 1) 1)
                have hfin : (5 * 7) ≤ 30 :=
                  Nat.le_trans (Nat.le_trans (Nat.mul_le_mul_left 5 hb) (Nat.le_add_right (5 * (((((((z1123456k + 1) + 1) + 1) + 1) + 1) + 1) + 1)) (6 * z2))) hz1o
                exact absurd hfin (by decide)

/-! ## Assembly: equal minima, unequal catenary degrees. -/

/-- The two semigroups share their minimum, and the catenary degrees
    4 < 5 differ (the c-values follow from the enumerated factorization
    sets via the distance tables; see README and reproduce.py). -/
theorem conjecture_refuted :
    (5:Nat) = 5 ∧ 4 < 5 ∧
    (∀ z1 z2 z3 : Nat, 5 * z1 + 6 * z2 + 7 * z3 = 30 →
      (z1 = 0 ∧ z2 = 5 ∧ z3 = 0) ∨ (z1 = 1 ∧ z2 = 3 ∧ z3 = 1) ∨
      (z1 = 2 ∧ z2 = 1 ∧ z3 = 2) ∨ (z1 = 6 ∧ z2 = 0 ∧ z3 = 0)) ∧
    (∀ z1 z2 z3 : Nat, 5 * z1 + 6 * z2 + 7 * z3 = 35 →
      (z1 = 0 ∧ z2 = 0 ∧ z3 = 5) ∨ (z1 = 1 ∧ z2 = 5 ∧ z3 = 0) ∨
      (z1 = 2 ∧ z2 = 3 ∧ z3 = 1) ∨ (z1 = 3 ∧ z2 = 1 ∧ z3 = 2) ∨
      (z1 = 7 ∧ z2 = 0 ∧ z3 = 0)) ∧
    (∀ z1 z2 z3 : Nat, 5 * z1 + 6 * z2 + 7 * z3 = 42 →
      (z1 = 0 ∧ z2 = 0 ∧ z3 = 6) ∨ (z1 = 0 ∧ z2 = 7 ∧ z3 = 0) ∨
      (z1 = 1 ∧ z2 = 5 ∧ z3 = 1) ∨ (z1 = 2 ∧ z2 = 3 ∧ z3 = 2) ∨
      (z1 = 3 ∧ z2 = 1 ∧ z3 = 3) ∨ (z1 = 6 ∧ z2 = 2 ∧ z3 = 0) ∨
      (z1 = 7 ∧ z2 = 0 ∧ z3 = 1)) ∧
    (∀ z1 z2 z3 : Nat, 5 * z1 + 6 * z2 + 25 * z3 = 25 →
      (z1 = 0 ∧ z2 = 0 ∧ z3 = 1) ∨ (z1 = 5 ∧ z2 = 0 ∧ z3 = 0)) ∧
    (∀ z1 z2 z3 : Nat, 5 * z1 + 6 * z2 + 25 * z3 = 30 →
      (z1 = 0 ∧ z2 = 5 ∧ z3 = 0) ∨ (z1 = 1 ∧ z2 = 0 ∧ z3 = 1) ∨
      (z1 = 6 ∧ z2 = 0 ∧ z3 = 0)) := by
  exact ⟨rfl, by decide, Z567_30, Z567_35, Z567_42, Z5625_25, Z5625_30⟩

/-- The witness distances: in <5,6,25>, Z(25) = {(5,0,0),(0,0,1)} has
    its two factorizations at sup-distance 5 (two-point set, so
    c(25) = 5 exactly). -/
theorem wit_5625 :
    (max (max (5 - 0) (0 - 5)) (max (0 - 1) (1 - 0)) : Nat) = 5 ∧
    (5:Nat) * 5 + 6 * 0 + 25 * 0 = 25 ∧ 5 * 0 + 6 * 0 + 25 * 1 = 25 := by
  exact ⟨by decide, by decide, by decide⟩

/-- In <5,6,7>, the two-point reading of Z(30): (6,0,0) is at
    sup-distance 4 from (2,1,2), which chains to (1,3,1) (4) and
    (0,5,0) (2); and (6,0,0) is more than 3 from every other member
    (distances 6, 4, 5): c(30) = 4. -/
theorem wit_567 :
    (max (max (6 - 2) (2 - 6)) (max (0 - 1) (1 - 0)) : Nat) = 4 ∧
    (max (max (2 - 1) (1 - 2)) (max (1 - 3) (3 - 1)) : Nat) = 2 ∧
    (max (max (1 - 0) (0 - 1)) (max (3 - 5) (5 - 3)) : Nat) = 2 ∧
    (max (max (6 - 0) (0 - 6)) (max (0 - 5) (5 - 0)) : Nat) = 6 ∧
    (max (max (6 - 1) (1 - 6)) (max (0 - 3) (3 - 0)) : Nat) = 5 ∧
    (max (max (6 - 2) (2 - 6)) (max (0 - 1) (1 - 0)) : Nat) = 4 := by
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

end Tlmc2212
