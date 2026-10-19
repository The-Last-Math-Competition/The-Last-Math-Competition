import Core
namespace TLMC8872

/-- The actual disjunctive sum: on a turn exactly one summand is played. -/
def add : (g h : Game) → Game
  | .node gl gr, .node hl hr => .node
      ((gl.attach.map fun x => add x.val (.node hl hr)) ++
        (hl.attach.map fun y => add (.node gl gr) y.val))
      ((gr.attach.map fun x => add x.val (.node hl hr)) ++
        (hr.attach.map fun y => add (.node gl gr) y.val))
termination_by g h => sizeOf g + sizeOf h
decreasing_by
  all_goals
    first
    | have h := List.sizeOf_lt_of_mem x.property; simp_wf; omega
    | have h := List.sizeOf_lt_of_mem y.property; simp_wf; omega

theorem zero_add (g : Game) : add zero g = g := by
  cases g with
  | node l r =>
    rw [zero, add]
    simp only [List.attach_nil, List.map_nil, List.nil_append]
    congr 1
    · apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.getElem_map, List.getElem_attach]
        exact zero_add _
    · apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.getElem_map, List.getElem_attach]
        exact zero_add _
termination_by sizeOf g
decreasing_by
  all_goals
    have h := List.sizeOf_lt_of_mem (List.getElem_mem (by assumption))
    simp_wf
    omega

theorem star_add_node (l r : List Game) :
    add star (.node l r) = .node
      ((.node l r) :: l.map (add star))
      ((.node l r) :: r.map (add star)) := by
  rw [star, add]
  simp [zero_add]

end TLMC8872
