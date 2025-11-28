import Mathlib.Tactic

inductive BinaryHeap (α : Type)
  | leaf : BinaryHeap α
  | node : BinaryHeap α → α → BinaryHeap α → BinaryHeap α

namespace BinaryHeap

def insert [Ord α] : α → BinaryHeap α → BinaryHeap α
| x, leaf => node leaf x leaf
| x, node l key r =>
    if Ord.compare x key == Ordering.lt then node l key (insert x r)
    else node (insert x l) key r


/--
Checks the min-heap property: for every node, its key is ≤ the keys of its children.
-/
def isMinHeap [Ord α] : BinaryHeap α → Bool
| leaf => true
| node l key r =>
    let leftOk := match l with
      | leaf => true
      | node _ lkey _ => Ord.compare key lkey ≠ Ordering.gt ∧ isMinHeap l
    let rightOk := match r with
      | leaf => true
      | node _ rkey _ => Ord.compare key rkey ≠ Ordering.gt ∧ isMinHeap r
    leftOk && rightOk


theorem insert_preserves_isMinHeap [Ord α] (x : α) (h : BinaryHeap α) :
  isMinHeap h → isMinHeap (insert x h) := by
  induction h with
  | leaf =>
    intro _
    simp [insert, isMinHeap]
  | node left key right ih_left ih_right =>
    intro H
    simp [insert]
    split
    · expose_names
      simp [isMinHeap]
      cases left with
      | leaf =>
        simp
        cases right with
        | leaf =>
          simp [insert]
          simp_all [isMinHeap, insert]
          apply?
          sorry
        | node right_left right_key right_right =>
          expose_names
          simp [insert]
          simp_all [isMinHeap, insert, compare]
          sorry
      | node left_left left_key left_right =>
        simp
        cases right with
        | leaf =>
          simp [insert]
          sorry
        | node right_left right_key right_right =>
          expose_names
          simp [insert]
          sorry
    · expose_names
      simp [isMinHeap]
      sorry
