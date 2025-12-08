import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Walk
import Mathlib.Combinatorics.SimpleGraph.Metric

inductive BinaryTree (α : Type u)
  | leaf : BinaryTree α
  | node : BinaryTree α → α → BinaryTree α → BinaryTree α

structure BinaryHeap (α : Type u) where
  tree : BinaryTree α

namespace BinaryHeap
def empty {α : Type u} : BinaryHeap α := { tree := BinaryTree.leaf }
set_option linter.unusedVariables false
def add {α : Type u} (h : BinaryHeap α) (v : α) (priority : Nat) : BinaryHeap α := sorry
noncomputable def extract_min {α : Type u} [Nonempty α] (h : BinaryHeap α) : (α × BinaryHeap α) :=sorry

def sizeOf {α : Type u} (h : BinaryHeap α) : Nat := sorry
def isEmpty {α : Type u} (h : BinaryHeap α) : Bool := sorry
def decrease_priority (h: BinaryHeap α) (v : V) (n : Nat) : BinaryHeap α := sorry
end BinaryHeap

structure FinSimpleGraph (V : Type u) [Fintype V] [DecidableEq V]  extends SimpleGraph V

noncomputable
instance  fintypeFinSimpleGraph {V : Type u} [Fintype V] [DecidableEq V] (G : FinSimpleGraph V) (v : V): Fintype (G.neighborSet v) :=  Fintype.ofFinite ↑(G.neighborSet v)


open Finset SimpleGraph BinaryHeap


variable  {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def relaxNeighbors (g : FinSimpleGraph V) (u : V) (dist : V → Nat) (queue : BinaryHeap V) : (V → Nat) × (BinaryHeap V) :=
  List.foldl
    (fun (acc : (V → Nat) × BinaryHeap V) (v : V) =>
      let (dist, queue) := acc
      let alt := dist u + 1
      if alt < dist v then
        let dist' : V → Nat := fun x => if x = v then alt else dist x
        let queue' := queue.decrease_priority v alt
        (dist', queue')
      else
        (dist, queue)
    )
    (dist, queue)
    (g.neighborFinset u).val.toList


noncomputable def dijkstra_rec [Nonempty V] (g: FinSimpleGraph V) (source : V) (target : V) (dist : V → Nat) (queue : BinaryHeap V) : V → Nat :=
  if queue.isEmpty then dist
  else
    let (u, queue') := queue.extract_min
    let (dist', queue'') := relaxNeighbors g u dist queue'
    dijkstra_rec g source target dist' queue''
decreasing_by sorry


noncomputable def dijkstra [Nonempty V] (g : FinSimpleGraph V) (source : V) (target : V) : V → Nat  :=
  let inf := 1000000000 -- a large value to represent "infinity"
  let dist : V → Nat := fun v => if v = source then 0 else inf -- distance map
  let queue := BinaryHeap.empty.add source 0 -- initialize BinaryHeap with source at priority 0
  dijkstra_rec g source target dist queue

/-!
Correctness of Dijkstra's algorithm on unweighted graphs.
We state the theorem using the graph distance from Mathlib (`SimpleGraph.dist`).
The proof will be provided once the BinaryHeap operations and termination are fully implemented.
-/

noncomputable def delta (g : FinSimpleGraph V) (s v : V) : Nat :=
  (SimpleGraph.dist (G := (by exact g.toSimpleGraph)) s v)

theorem dijkstra_correctness
  [Nonempty V]
  (g : FinSimpleGraph V) (s : V) :
  ∀ v : V, dijkstra g s v = delta g s v := by
  intro v
  -- Proof sketch: By induction on the number of extract-min operations.
  -- Use the invariant that dist[u] is finalized when u is extracted,
  -- and every relaxation preserves upper bounds and eventually reaches the true distance.
  -- This relies on the correctness of the BinaryHeap operations and termination of `dijkstra_rec`.
  sorry
