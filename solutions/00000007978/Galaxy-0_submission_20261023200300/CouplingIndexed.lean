import Coupling
import Approx
set_option autoImplicit false
namespace PIR
theorem natSum_ofFn (R : Nat) (f : Fin R → Nat) : natSum (List.ofFn f) = total R f := by
  induction R with
  | zero => simp [List.ofFn_zero, natSum, total]
  | succ R ih => simp only [List.ofFn_succ, natSum, total, ih]; rfl

theorem indexed_coupling {R : Nat} {Q : Type} [DecidableEq Q]
    (query reference : Fin R → Q)
    (privacy : ∀ q, (List.ofFn query).count q = (List.ofFn reference).count q) :
    ∃ relabel : Fin R → Fin R,
      (∀ r, query (relabel r) = reference r) ∧
      (∀ cost : Fin R → Nat, total R (fun r => cost (relabel r)) = total R cost) := by
  let seeds : List (Fin R) := List.ofFn id
  have hmap : seeds.map query = List.ofFn query := by simp [seeds, List.map_ofFn]
  obtain ⟨reordered, hr, hq, hcost⟩ := coupling_from_equal_query_counts query
    (List.ofFn reference) seeds (by simpa only [hmap] using privacy)
  have hlen : reordered.length = R := by
    have hh := hr.length_eq
    simpa [seeds] using hh
  let relabel : Fin R → Fin R := fun r => reordered[r.val]'(by rw [hlen]; exact r.isLt)
  have hlist : List.ofFn relabel = reordered := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i h1 h2
      simp only [List.getElem_ofFn]
      rfl
  refine ⟨relabel, ?_, ?_⟩
  · intro r
    have hm : List.ofFn (fun i => query (relabel i)) = List.ofFn reference := by
      change List.ofFn (query ∘ relabel) = _
      rw [← List.map_ofFn, hlist, hq]
    have hv := congrArg (fun xs : List Q => xs[r.val]?) hm
    simpa only [List.getElem?_ofFn, dif_pos r.isLt, Option.some.injEq] using hv
  · intro cost
    have hc := hcost cost
    rw [← hlist, List.map_ofFn] at hc
    have hs : seeds.map cost = List.ofFn cost := by simp [seeds, List.map_ofFn]
    rw [hs, natSum_ofFn, natSum_ofFn] at hc
    exact hc


#print axioms indexed_coupling
end PIR
