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


--def treeMin:  BinaryTree α → (α → ENat) → Option α
--| leaf, _ => none
--| node l v r, f => alphaMapMin (λx: if x = some x' then f x' else ⊤) v (alphaMapMin f (treeMin l f) (treeMin r f))

-- lemma extractMinCorrectNode (bt l r: BinaryTree α) (v: α) (f: α → ENat): bt = node l v r  → isMinHeap bt f → ∃ bt', extractMin bt f = (some (treeMin bt f), bt') ∧ isMinHeap bt' f := by sorry
def rootIsMinOfChildren: (BinaryTree α) → (α → ENat) →  Prop
| leaf, _ => true
| node l v r, f => match l, r with
    | leaf, leaf => true
    | leaf, node _ rv _ => f v <= f rv
    | node _ lv _, leaf => f v <= f lv
    | node _ lv _, node _ rv _ =>  f v <= f lv ∧ f v <= f rv

def isEmpty (bt: BinaryTree α):= bt = leaf

def leftAndRightAreMinHeap: (BinaryTree α) →  (f: α → ENat) →  Prop
| leaf, _ => true
| node l _ r, f => isMinHeap l f ∧ isMinHeap r f


lemma minHeapThenLeftAndRightAreMinHeap (bt: BinaryTree α) (f: α → ENat): isMinHeap bt f → leftAndRightAreMinHeap bt f := by
intro hbt
fun_induction isMinHeap; all_goals (grind [leftAndRightAreMinHeap, isMinHeap])

lemma minHeapThenRootIsMinOfChildren (bt: BinaryTree α) (f: α → ENat): isMinHeap bt f → rootIsMinOfChildren bt f := by
intro hbt
fun_induction isMinHeap; all_goals (grind [rootIsMinOfChildren])


lemma leftAndRightAreMinHeapAndRootIsMinOfChildrenToMinHeap (bt: BinaryTree α) (f: α → ENat): leftAndRightAreMinHeap bt f ∧ rootIsMinOfChildren bt f → isMinHeap bt f := by
intro hbt
fun_induction isMinHeap; all_goals (simp [rootIsMinOfChildren, leftAndRightAreMinHeap] at hbt;simp[hbt])

lemma leftAndRightAreMinHeapLeft (l: BinaryTree α) (r: BinaryTree α) (v: α) (f: α → ENat): leftAndRightAreMinHeap (node l v r) f → leftAndRightAreMinHeap l f := by
intro hbt
simp [leftAndRightAreMinHeap] at hbt
simp [minHeapThenLeftAndRightAreMinHeap, hbt]


lemma leftAndRightAreMinHeapRight (l: BinaryTree α) (r: BinaryTree α) (v: α) (f: α → ENat): leftAndRightAreMinHeap (node l v r) f → leftAndRightAreMinHeap r f := by
intro hbt
simp [leftAndRightAreMinHeap] at hbt
simp [minHeapThenLeftAndRightAreMinHeap, hbt]

lemma heapifyPreservesStructure (bt: BinaryTree α) (f: α → ENat): (∃ l r v, bt = node l v r) →  ∃ l' v' r', heapify bt f = node l' v' r' := by
intro hbt
fun_induction heapify; all_goals expose_names
. obtain ⟨l, r, v, hbt⟩ := hbt
  contradiction
all_goals simp



lemma heapifyPreservesStructureAndRootMin (bt: BinaryTree α) (f: α → ENat): (∃ l r v, bt = node l v r) →  ∃ l' v' r', heapify bt f = node l' v' r' ∧ f v' ≤ (heapMin bt f) := by
intro hbt
fun_induction heapify; all_goals expose_names
. obtain ⟨l, r, v, hbt⟩ := hbt
  contradiction
all_goals grind [heapMin]

def contains: (BinaryTree α) → α → Prop
| leaf, _ => false
| node l v r, v' => v=v' ∨ contains l v' ∨ contains r v'

lemma heapifyPreservesMembers (bt: BinaryTree α) (v: α) (f: α → ENat): contains bt v → contains (heapify bt f) v := by
intro hbt
fun_induction heapify generalizing v; all_goals try grind[contains]

lemma heapifyPreservesMembers2 (bt: BinaryTree α) (v: α) (f: α → ENat):  contains (heapify bt f) v → contains bt v := by
intro hbt
fun_induction heapify generalizing v; all_goals try grind[contains]

lemma containsIsNode (bt: BinaryTree α) (v: α): contains bt v → ∃ l v' r, bt = node l v' r := by
fun_induction contains; all_goals simp

lemma minHeapRootMin (bt l r: BinaryTree α) (v: α) (f: α → ENat): bt = (node l v r) → isMinHeap bt f → f v = heapMin bt f := by
intro hbt hmin
fun_induction isMinHeap; all_goals grind [heapMin]

lemma rootIsMinOfChildrenLeft (l r ll lr: BinaryTree α) (v lv: α) (f: α → ENat): rootIsMinOfChildren (node l v r) f →  l = (node ll lv lr) →  f v ≤ f lv := by
  intros; expose_names
  rw [h_1] at h
  cases r; all_goals grind[rootIsMinOfChildren]


lemma rootIsMinOfChildrenRight (l r rl rr: BinaryTree α) (v rv: α) (f: α → ENat): rootIsMinOfChildren (node l v r) f →  r = (node rl rv rr) → f v ≤ f rv := by
  intros; expose_names
  rw [h_1] at h
  cases r; all_goals try grind[rootIsMinOfChildren]
  . grind [rootIsMinOfChildren.eq_def]


lemma minHeapMemberLeRoot (bt: BinaryTree α) (v: α) (f: α → ENat): isMinHeap bt f →  contains bt v →  heapMin bt f ≤ f v := by
intro hmin hl
fun_induction contains
. contradiction
. expose_names
  cases hl; all_goals expose_names
  . expose_names
    rw [←h]
    suffices f v = (l.node v r).heapMin f by grind
    apply minHeapRootMin (l.node v r) l r v; all_goals grind
  . cases h; all_goals expose_names
    . have h2: l.contains v' := by exact h
      apply containsIsNode at h2
      obtain ⟨l'', v'', r'', h2 ⟩:= h2
      have h3: l = l''.node v'' r'' := by exact h2
      have hmin2: (l.node v r).isMinHeap f := by assumption
      have hmin3: (l.node v r).isMinHeap f := by assumption
      apply minHeapThenLeftAndRightAreMinHeap at hmin
      simp [leftAndRightAreMinHeap] at hmin
      have hlmin: l.isMinHeap f:= by grind
      have hlmin2: l.isMinHeap f:= by grind
      apply ih2 at hlmin
      apply hlmin at h
      grw[← h]
      apply minHeapThenRootIsMinOfChildren at hmin2
      apply rootIsMinOfChildrenLeft l r l'' r'' v v'' f hmin2 at h2
      have hhl: f v'' = l.heapMin f:= by grind [minHeapRootMin]
      have hh: f v = (l.node v r).heapMin f:= by grind [minHeapRootMin]
      grw [← hh, ← hhl]
      exact h2
    . have h2: r.contains v' := by exact h
      apply containsIsNode at h2
      obtain ⟨l'', v'', r'', h2 ⟩:= h2
      have h3: r = l''.node v'' r'' := by exact h2
      have hmin2: (l.node v r).isMinHeap f:= by assumption
      have hmin3: (l.node v r).isMinHeap f:= by assumption
      apply minHeapThenLeftAndRightAreMinHeap at hmin
      simp [leftAndRightAreMinHeap] at hmin
      have hlmin: r.isMinHeap f:= by grind
      have hlmin2: r.isMinHeap f:= by grind
      apply ih1 at hlmin
      apply hlmin at h
      grw[← h]
      apply minHeapThenRootIsMinOfChildren at hmin2
      apply rootIsMinOfChildrenRight l r l'' r'' v v'' f hmin2 at h2
      have hhl: f v'' = r.heapMin f:= by grind [minHeapRootMin]
      have hh: f v = (l.node v r).heapMin f:= by grind [minHeapRootMin]
      grw [← hh, ← hhl]
      exact h2

-- lemma heapifyEstablishesRootIsMinOfChildren (bt: BinaryTree α) (hbt: leftAndRightAreMinHeap bt): rootIsMinOfChildren (heapify bt f) := by
-- fun_induction heapify; all_goals expose_names; all_goals try grind[rootIsMinOfChildren, leftAndRightAreMinHeap]
-- .
--  have hr: (rl.node rv rr).leftAndRightAreMinHeap := by
--     grind [leftAndRightAreMinHeapRight]
--   simp [leftAndRightAreMinHeap] at hr
--   simp [leftAndRightAreMinHeap] at ih1
--   obtain ⟨hr1, hr2⟩ := hr
--   apply ih1 at hr1
--   apply hr1 at hr2
--   have: ∃ l' v' r', heapify (node rl v rr) = node l' v' r' := by
--     simp [heapifyPreservesStructure (node rl v rr)]
--   obtain ⟨rl', v', rr', hrw⟩ := this
--   rw [hrw]
--   simp[rootIsMinOfChildren]
--   grw[h]
--   rw [hrw] at hr2
--   have: contains (node rl' v' rr') v := by
--     rw [←hrw]
--     apply heapifyPreservesMembers
--     simp [contains]



--   sorry
-- all_goals sorry

-- lemma heapifyEstablishesLeftAndRigthAreMinHeap (bt: BinaryTree α) (hbt: leftAndRightAreMinHeap bt): leftAndRightAreMinHeap (heapify bt f) := by
-- fun_induction heapify; all_goals expose_names
-- . simp [leftAndRightAreMinHeap]
-- . simp [leftAndRightAreMinHeap, isMinHeap]
-- . simp [leftAndRightAreMinHeap, isMinHeap]
--   simp [leftAndRightAreMinHeap] at hbt
--   have hbtr: (rl.node rv rr).leftAndRightAreMinHeap := by grind [←minHeapThenLeftAndRightAreMinHeap]
--   apply ih1 at hbtr
--   sorry
-- all_goals sorry

--lemma leftAndRightAreMinHeapAndRootIsMinImpliesIsHeap ()

lemma heapifyPreservesMinHeap (bt: BinaryTree α) (f: α → ENat): isMinHeap bt f → bt = heapify bt f:= by
fun_induction heapify; all_goals expose_names; all_goals try grind
. intro hbt
  by_contra
  have hbtmin: f v = heapMin (leaf.node v (rl.node rv rr)) f:= by grind [minHeapRootMin]
  grind[heapMin]
. intro hbt
  by_contra
  have hbtmin: f v = heapMin ((ll.node lv lr).node v leaf) f:= by grind [minHeapRootMin]
  grind[heapMin]
. intro hbt
  have hbtmin: f v = heapMin ((ll.node lv lr).node v (rl.node rv rr)) f:= by grind [minHeapRootMin]
  grind[heapMin]
. intro hbt
  have hbtmin: f v = heapMin ((ll.node lv lr).node v (rl.node rv rr)) f:= by grind [minHeapRootMin]
  grind[heapMin]

lemma binTreeEqR (l r l' r': BinaryTree α) (v v': α): (node l v r) = (node l' v' r') → r = r' := by
grind only

lemma binTreeEqL (l r l' r': BinaryTree α) (v v': α): (node l v r) = (node l' v' r') → l = l' := by
grind only

-- lemma decreaseRootIsHeap (l r: BinaryTree α) (v v':  α): isMinHeap (node l v r) →  v' ≤ minHeap (node l v r) → isMinHeap (node l v' r) := by sorry

lemma heapifyPreservesValues (tree r l: BinaryTree α) (v: α) (f: α → ENat): tree.heapify f = node r v l → contains tree v := by
grind [contains, heapifyPreservesMembers2]

lemma containsRootOrChildren (tree r l: BinaryTree α) (v v': α) : tree = node r v l → contains tree v' → contains r v' ∨ contains l v' ∨ v= v' := by
grind [contains]


lemma containsRootOrChildrenLeftLeaf (tree r: BinaryTree α) (v v':  α): tree = node r v leaf → contains tree v' → contains r v' ∨ v= v' := by
grind [contains]

lemma containsRightThenContainsRoot (tree l r: BinaryTree α) (v v':  α): tree = node l v r → contains r v' → contains tree v' := by
grind [contains]

lemma containsLeftThenContainsRoot (tree l r: BinaryTree α) (v v':  α): tree = node l v r → contains l v' → contains tree v' := by
grind [contains]

lemma heapifyEstablishesMinHeap' (bt l r: BinaryTree α) (v: α) (f: α → ENat): bt = node l v r ∧  isMinHeap l f ∧ isMinHeap r f → isMinHeap (heapify bt f) f := by
fun_induction heapify generalizing l r v; all_goals expose_names
. simp [isMinHeap]
. simp [isMinHeap]
. intro ⟨hr, hminl, hminr⟩
  apply leftAndRightAreMinHeapAndRootIsMinOfChildrenToMinHeap
  have: ∃ rl' v' rr', (rl.node v_1 rr).heapify f = node rl' v' rr' ∧ f v' ≤ heapMin (rl.node v_1 rr) f:= by
        apply heapifyPreservesStructureAndRootMin
        simp
  obtain ⟨rl', v', rr', hr1, hr2⟩ := this
  have hv: v=v_1 := by grind
  have hrnode: r = (rl.node rv rr) := by
        apply binTreeEqR at hr
        simp [hr]
  constructor
  . simp [leftAndRightAreMinHeap]
    constructor
    . simp [isMinHeap]
    . specialize ih1 rl rr v_1
      simp at ih1
      apply minHeapThenLeftAndRightAreMinHeap at hminr
      simp [leftAndRightAreMinHeap] at hminr
      simp [hrnode] at hminr
      apply ih1; all_goals grind
  . rw [hr1]
    simp [rootIsMinOfChildren]
    have hrvmin : f rv = heapMin (rl.node rv rr) f:= by
      apply minHeapRootMin (rl.node rv rr) rl rr rv f (rfl)
      rw[← hrnode]; exact hminr
    have hcontains: contains (node rl v_1 rr) v' := by
      apply heapifyPreservesMembers2
      rw[hr1]
      simp[contains]
    have hcontains: contains (rl.node rv rr) v' ∨ v'= v_1 := by grind[contains]
    cases hcontains
    . expose_names
      apply minHeapMemberLeRoot r v' at hminr
      rw [← hrnode] at h_1
      apply hminr at h_1
      grw[← h_1]
      rw[hrvmin]
      rw[hrnode]
    . expose_names
      rw [h_1]
      grw [h]
. grind [isMinHeap]
. intro ⟨hl, hminl, hminr⟩
  apply leftAndRightAreMinHeapAndRootIsMinOfChildrenToMinHeap
  have: ∃ ll' v' lr', (ll.node v_1 lr).heapify f = node ll' v' lr' ∧ f v' ≤ heapMin (ll.node v_1 lr) f:= by
        apply heapifyPreservesStructureAndRootMin
        simp
  obtain ⟨rl', v', rr', hr1, hr2⟩ := this
  have hv: v=v_1 := by grind
  have hlnode: l = (ll.node lv lr) := by
        apply binTreeEqL at hl
        simp [hl]
  constructor
  . simp [leftAndRightAreMinHeap]
    constructor
    . specialize ih1 ll lr v_1
      simp at ih1
      apply minHeapThenLeftAndRightAreMinHeap at hminl
      simp [leftAndRightAreMinHeap] at hminl
      simp [hlnode] at hminl
      apply ih1; all_goals grind
    . simp [isMinHeap]
  . rw [hr1]
    simp [rootIsMinOfChildren]
    have hlvmin : f lv = heapMin (ll.node lv lr) f:= by
      apply minHeapRootMin (ll.node lv lr) ll lr lv f (rfl)
      rw[← hlnode]; exact hminl
    have hcontains: contains (node ll v_1 lr) v' := by
      apply heapifyPreservesMembers2
      rw[hr1]
      simp[contains]
    have hcontains: contains (ll.node lv lr) v' ∨ v'= v_1 := by grind[contains]
    cases hcontains
    . expose_names
      apply minHeapMemberLeRoot l v' at hminl
      rw [← hlnode] at h_1
      apply hminl at h_1
      grw[← h_1]
      rw[hlvmin]
      rw[hlnode]
    . expose_names
      rw [h_1]
      grw [h]
. grind [isMinHeap]
. grind [isMinHeap]
. intro ⟨hl, hminl, hminr⟩
  apply leftAndRightAreMinHeapAndRootIsMinOfChildrenToMinHeap
  have: ∃ ll' v' lr', (ll.node v_1 lr).heapify f = node ll' v' lr' ∧ f v' ≤ heapMin (ll.node v_1 lr) f:= by
        apply heapifyPreservesStructureAndRootMin
        simp
  obtain ⟨rl', v', rr', hr1, hr2⟩ := this
  have hv: v=v_1 := by grind
  have hlnode: l = (ll.node lv lr) := by
        apply binTreeEqL at hl
        simp [hl]
  constructor
  . simp [leftAndRightAreMinHeap]
    constructor
    . specialize ih1 ll lr v_1
      simp at ih1
      apply minHeapThenLeftAndRightAreMinHeap at hminl
      simp [leftAndRightAreMinHeap] at hminl
      simp [hlnode] at hminl
      apply ih1; all_goals grind
    . grind
  . rw [hr1]
    simp [rootIsMinOfChildren]
    have hlvmin : f lv = heapMin (ll.node lv lr) f := by
      apply minHeapRootMin (ll.node lv lr) ll lr lv f (rfl)
      rw[← hlnode]; exact hminl
    have hcontains: contains (node ll v_1 lr) v' := by
      apply heapifyPreservesMembers2
      rw[hr1]
      simp[contains]
    have hcontains: contains (ll.node lv lr) v' ∨ v'= v_1 := by grind[contains]
    cases hcontains
    . expose_names
      apply minHeapMemberLeRoot l v' at hminl
      grind
    . expose_names
      grind
. grind [isMinHeap]
. intro ⟨hr, hminl, hminr⟩
  apply leftAndRightAreMinHeapAndRootIsMinOfChildrenToMinHeap
  have: ∃ rl' v' rr', (rl.node v_1 rr).heapify f = node rl' v' rr' ∧ f v' ≤ heapMin (rl.node v_1 rr) f:= by
        apply heapifyPreservesStructureAndRootMin
        simp
  obtain ⟨rl', v', rr', hr1, hr2⟩ := this
  have hv: v=v_1 := by grind
  have hrnode: r = (rl.node rv rr) := by
        apply binTreeEqR at hr
        simp [hr]
  constructor
  . simp [leftAndRightAreMinHeap]
    constructor
    . grind
    . specialize ih1 rl rr v_1
      simp at ih1
      apply minHeapThenLeftAndRightAreMinHeap at hminr
      simp [leftAndRightAreMinHeap] at hminr
      simp [hrnode] at hminr
      apply ih1
      . grind
      . obtain ⟨h1, h2⟩ := hminr
        exact h2
  . rw [hr1]
    simp [rootIsMinOfChildren]
    have hrvmin : f rv = heapMin (rl.node rv rr) f := by
      apply minHeapRootMin (rl.node rv rr) rl rr rv f (rfl)
      rw[← hrnode]; exact hminr
    have hcontains: contains (node rl v_1 rr) v' := by
      apply heapifyPreservesMembers2
      rw[hr1]
      simp[contains]
    have hcontains: contains (rl.node rv rr) v' ∨ v'= v_1 := by
      apply containsRootOrChildren (node rl v_1 rr) rl rr v_1 v' (rfl) at hcontains
      cases hcontains; all_goals expose_names
      . left
        apply containsLeftThenContainsRoot (node rl rv rr) rl rr rv v' (rfl) (h_2)
      . cases h_2; all_goals expose_names
        . left
          apply containsRightThenContainsRoot (node rl rv rr) rl rr rv v' (rfl) (h_2)
        . right
          rw [h_2]
    constructor
    . simp at h
      grw [h]
    cases hcontains
    . expose_names
      apply minHeapMemberLeRoot r v' at hminr
      rw [← hrnode] at h_2
      apply hminr at h_2
      grw[← h_2]
      rw[hrvmin]
      rw[hrnode]
    . expose_names
      rw [h_2]
      simp at h_1
      grw [h_1]

lemma heapifyEstablishesMinHeap (bt: BinaryTree α) (f: α → ENat): (hbt: leftAndRightAreMinHeap bt f) → isMinHeap (heapify bt f) f := by
cases bt
. grind[isMinHeap,leftAndRightAreMinHeap, heapify]
. grind[isMinHeap,leftAndRightAreMinHeap, heapifyEstablishesMinHeap']
