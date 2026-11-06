import FieldTables
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Algebra.IsPrimePow

namespace Steiner1029

theorem firstFieldTable_exists_prime_power (p m : Nat)
    (hp : p.Prime) (hm : 0 < m) :
    Exists fun t => firstFieldTable (p ^ m) = some t := by
  classical
  let : Fact p.Prime := Fact.mk hp
  let : Fintype (GaloisField p m) := Fintype.ofFinite (GaloisField p m)
  have hcard : Fintype.card (GaloisField p m) = p ^ m := by
    simpa only [Nat.card_eq_fintype_card] using (GaloisField.card p m hm.ne')
  exact firstFieldTable_exists_of_model (GaloisField p m) (p ^ m) hcard

theorem firstFieldTable_exists_of_prime_power (q : Nat)
    (h : Exists fun p => Exists fun m =>
      p.Prime /\ 0 < m /\ q = p ^ m) :
    Exists fun t => firstFieldTable q = some t := by
  cases h with
  | intro p h =>
      cases h with
      | intro m h =>
          rw [h.2.2]
          exact firstFieldTable_exists_prime_power p m h.1 h.2.1

theorem firstFieldTable_exists_of_isPrimePow (q : Nat) (hq : IsPrimePow q) :
    Exists fun t => firstFieldTable q = some t := by
  cases (isPrimePow_nat_iff q).mp hq with
  | intro p h =>
      cases h with
      | intro m h =>
          rw [<- h.2.2]
          exact firstFieldTable_exists_prime_power p m h.1 h.2.1

theorem firstFieldTable_valid_exists_of_isPrimePow (q : Nat) (hq : IsPrimePow q) :
    Exists fun t => firstFieldTable q = some t /\ TableValid t := by
  cases firstFieldTable_exists_of_isPrimePow q hq with
  | intro t ht =>
      exact Exists.intro t (And.intro ht (firstFieldTable_valid ht))

end Steiner1029

#check Steiner1029.firstFieldTable_exists_prime_power
#print axioms Steiner1029.firstFieldTable_exists_prime_power
#check Steiner1029.firstFieldTable_exists_of_prime_power
#print axioms Steiner1029.firstFieldTable_exists_of_prime_power
#check Steiner1029.firstFieldTable_exists_of_isPrimePow
#print axioms Steiner1029.firstFieldTable_exists_of_isPrimePow
#check Steiner1029.firstFieldTable_valid_exists_of_isPrimePow
#print axioms Steiner1029.firstFieldTable_valid_exists_of_isPrimePow
#check GaloisField.card
#print axioms GaloisField.card
#check Steiner1029.firstFieldTable_exists_of_model
#print axioms Steiner1029.firstFieldTable_exists_of_model
#print Steiner1029.firstFieldTable
#print axioms Steiner1029.firstFieldTable
