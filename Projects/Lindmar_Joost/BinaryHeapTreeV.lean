import Mathlib.Tactic
#check Nat.div2Induction
#check ENat

inductive BinaryTree (α : Type)
  | leaf : BinaryTree α
  | node : BinaryTree α → α → BinaryTree α → BinaryTree α

#check BinaryTree
set_option autoImplicit true
namespace BinaryTree

def isMinHeap : BinaryTree α → (dist : α → ENat) → Prop
| leaf, _ => true
| node l v r, f => match l, r with
      | leaf, leaf => true
      | node _ lv _, leaf => f v <= f lv ∧ isMinHeap l f
      | leaf, node _ rv _ => f v <= f rv ∧ isMinHeap r f
      | node _ lv _, node _ rv _ => f v <= f lv ∧ isMinHeap l f ∧ f v <= f rv ∧ isMinHeap r f

def heapify (bt: BinaryTree α) (f: α → ENat): BinaryTree α := match bt with
| leaf => bt
| node l v r => match l, r with
    | leaf, leaf => bt
    | leaf, node rl rv rr => if f rv < f v then node l rv (heapify (node rl v rr) f) else bt
    | node ll lv lr, leaf => if f lv < f v then node (heapify (node ll v lr) f) lv r else bt
    | node ll lv lr, node rl rv rr =>  if f lv <= f rv then
                                          if f v <= f lv then bt
                                          else node (heapify (node ll v lr) f) lv r
                                        else
                                          if f v <= f rv then bt
                                          else node l rv (heapify (node rl v rr) f)
def getLast: BinaryTree α → Option α ×  BinaryTree α
| leaf => (none, leaf)
| node l v r => match l, r with
    | leaf, leaf => (some v, node l v r)
    | leaf, _ => let (val, tree) := (getLast r)
      (val, node l v tree)
    | _, _ => let (val, tree) := (getLast l)
      (val, node tree v r)


def extractMin (bt: BinaryTree α) (f: α → ENat): (Option α × BinaryTree α):=
let (lastNode, treeWithoutLast) := getLast bt
match lastNode with
| none => (none, leaf)
| some v' => match treeWithoutLast with
  | leaf => (some v', leaf)
  | node l v r => (some v, heapify (node l v' r) f)


def heapMin:  BinaryTree α → (α → ENat) → ENat
| leaf, _ => ⊤
| node l v r, f => match l, r with
    | leaf, leaf => (f v)
    | leaf, node _ rv _ => if f v <= f rv then f v else f rv
    | node _ lv _, leaf => if f v <= f lv then f v else f lv
    | node _ lv _, node _ rv _ =>  if f lv <= f rv then
                                     if f v <= f lv then f v
                                     else f lv
                                    else
                                      if f v <= f rv then f v
                                      else f rv

def alphaMapMin (f: α → ENat) (a b: α): α  := if f a <=f b then a else b


def treeMin:  BinaryTree α → (α → ENat) → Option α
| leaf, _ => none
| node l v r, f => alphaMapMin (λx: if x = some x' then f x' else ⊤) v (alphaMapMin f (treeMin l f) (treeMin r f))

lemma extractMinCorrectNode (bt l r: BinaryTree α) (v: α) (f: α → ENat): bt = node l v r  → isMinHeap bt f → ∃ bt', extractMin bt f = (some (treeMin bt f), bt') ∧ isMinHeap bt' f := by sorry

def isEmpty (bt: BinaryTree ENat):= bt = leaf

def leftAndRightAreMinHeap: (BinaryTree α) →  (f: α → ENat) →  Prop
| leaf, _ => true
| node l _ r, f => isMinHeap l f ∧ isMinHeap r f

lemma heapifyEstablishesMinHeap (bt: BinaryTree α) (f: α → ENat): (hbt: leftAndRightAreMinHeap bt f) → isMinHeap (heapify bt f) f := by sorry
