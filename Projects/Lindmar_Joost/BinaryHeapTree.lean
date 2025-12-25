import Mathlib.Tactic
#check Nat.div2Induction
#check ENat
inductive BinaryTree (α : Type)
  | leaf : BinaryTree α
  | node : BinaryTree α → α → BinaryTree α → BinaryTree α

namespace BinaryTree

def isMinHeap : BinaryTree ENat → Prop
| leaf => true
| node l v r => match l, r with
      | leaf, leaf => true
      | node _ lv _, leaf => v <= lv ∧ isMinHeap l
      | leaf, node _ rv _ => v <= rv ∧ isMinHeap r
      | node _ lv _, node _ rv _ => v <= lv ∧ isMinHeap l ∧ v <= rv ∧ isMinHeap r

def heapify (bt: BinaryTree ENat): BinaryTree ENat := match bt with
| leaf => bt
| node l v r => match l, r with
    | leaf, leaf => bt
    | leaf, node rl rv rr => if rv < v then node l rv (heapify (node rl v rr)) else bt
    | node ll lv lr, leaf => if lv < v then node (heapify (node ll v lr)) lv r else bt
    | node ll lv lr, node rl rv rr =>  if lv <= rv then
                                          if v <= lv then bt
                                          else node (heapify (node ll v lr)) lv r
                                        else
                                          if v <= rv then bt
                                          else node l rv (heapify (node rl v rr))

def extractMin: BinaryTree ENat → Option ENat
| leaf => none
| node _ v _ => some v

def heapMin:  BinaryTree ENat → ENat
| leaf => ⊤
| node l v r => match l, r with
    | leaf, leaf => v
    | leaf, node _ rv _ => if v <= rv then v else rv
    | node _ lv _, leaf => if v <= lv then v else lv
    | node _ lv _, node _ rv _ =>  if lv <= rv then
                                     if v <= lv then v
                                     else lv
                                    else
                                      if v <= rv then v
                                      else rv

def enatMin (n m: ENat): ENat  := if n<=m then n else m

def treeMin:  BinaryTree ENat → ENat
| leaf => ⊤
| node l v r => enatMin v (enatMin (treeMin l) (treeMin r))

def isEmpty (bt: BinaryTree ENat):= bt = leaf

def leftAndRightAreMinHeap: (BinaryTree ENat) →  Prop
| leaf => true
| node l _ r => isMinHeap l ∧ isMinHeap r

def rootIsMinOfChildren: (BinaryTree ENat) →  Prop
| leaf => true
| node l v r => match l, r with
    | leaf, leaf => true
    | leaf, node _ rv _ => v <= rv
    | node _ lv _, leaf => v <= lv
    | node _ lv _, node _ rv _ =>  v <= lv ∧ v <= rv

lemma minHeapThenLeftAndRightAreMinHeap (bt: BinaryTree ENat): isMinHeap bt → leftAndRightAreMinHeap bt := by
intro hbt
fun_induction isMinHeap; all_goals (grind [leftAndRightAreMinHeap, isMinHeap])

lemma minHeapThenRootIsMinOfChildren (bt: BinaryTree ENat): isMinHeap bt → rootIsMinOfChildren bt := by
intro hbt
fun_induction isMinHeap; all_goals (grind [rootIsMinOfChildren])


lemma leftAndRightAreMinHeapAndRootIsMinOfChildrenToMinHeap (bt: BinaryTree ENat): leftAndRightAreMinHeap bt ∧ rootIsMinOfChildren bt → isMinHeap bt := by
intro hbt
fun_induction isMinHeap; all_goals (simp [rootIsMinOfChildren, leftAndRightAreMinHeap] at hbt;simp[hbt])

lemma leftAndRightAreMinHeapLeft (l: BinaryTree ENat) (r: BinaryTree ENat) (v: ENat): leftAndRightAreMinHeap (node l v r) → leftAndRightAreMinHeap l := by
intro hbt
simp [leftAndRightAreMinHeap] at hbt
simp [minHeapThenLeftAndRightAreMinHeap, hbt]


lemma leftAndRightAreMinHeapRight (l: BinaryTree ENat) (r: BinaryTree ENat) (v: ENat): leftAndRightAreMinHeap (node l v r)  → leftAndRightAreMinHeap r := by
intro hbt
simp [leftAndRightAreMinHeap] at hbt
simp [minHeapThenLeftAndRightAreMinHeap, hbt]

lemma heapifyPreservesStructure (bt: BinaryTree ENat): (∃ l r v, bt = node l v r) →  ∃ l' v' r', heapify bt = node l' v' r' := by
intro hbt
fun_induction heapify; all_goals expose_names
. obtain ⟨l, r, v, hbt⟩ := hbt
  contradiction
all_goals simp



lemma heapifyPreservesStructureAndRootMin (bt: BinaryTree ENat): (∃ l r v, bt = node l v r) →  ∃ l' v' r', heapify bt = node l' v' r' ∧ v' ≤ (heapMin bt) := by
intro hbt
fun_induction heapify; all_goals expose_names
. obtain ⟨l, r, v, hbt⟩ := hbt
  contradiction
all_goals grind [heapMin]

def contains: (BinaryTree ENat) → ENat → Prop
| leaf, _ => false
| node l v r, v' => v=v' ∨ contains l v' ∨ contains r v'

lemma heapifyPreservesMembers (bt: BinaryTree ENat) (v: ENat): contains bt v → contains (heapify bt) v := by
intro hbt
fun_induction heapify generalizing v; all_goals try grind[contains]

lemma heapifyPreservesMembers2 (bt: BinaryTree ENat) (v: ENat):  contains (heapify bt) v → contains bt v := by
intro hbt
fun_induction heapify generalizing v; all_goals try grind[contains]

lemma containsIsNode (bt: BinaryTree ENat) (v: ENat): contains bt v → ∃ l v' r, bt = node l v' r := by
fun_induction contains; all_goals simp

lemma minHeapRootMin (bt l r: BinaryTree ENat) (v: ENat): bt = (node l v r) → isMinHeap bt → v = heapMin bt := by
intro hbt hmin
fun_induction isMinHeap; all_goals grind [heapMin]

lemma rootIsMinOfChildrenLeft (l r ll lr: BinaryTree ENat) (v lv: ENat): rootIsMinOfChildren (node l v r) →  l = (node ll lv lr) → v ≤ lv := by
  intros; expose_names
  rw [h_1] at h
  cases r; all_goals grind[rootIsMinOfChildren]


lemma rootIsMinOfChildrenRight (l r rl rr: BinaryTree ENat) (v rv: ENat): rootIsMinOfChildren (node l v r) →  r = (node rl rv rr) → v ≤ rv := by
  intros; expose_names
  rw [h_1] at h
  cases r; all_goals try grind[rootIsMinOfChildren]
  . grind [rootIsMinOfChildren.eq_def]


lemma minHeapMemberLeRoot (bt: BinaryTree ENat) (v: ENat):  isMinHeap bt →  contains bt v →  heapMin bt ≤ v := by
intro hmin hl
fun_induction contains
. contradiction
. expose_names
  cases hl; all_goals expose_names
  . expose_names
    rw [←h]
    suffices v = (l.node v r).heapMin by grind
    apply minHeapRootMin (l.node v r) l r v; all_goals grind
  . cases h; all_goals expose_names
    . have h2: l.contains v' := by exact h
      apply containsIsNode at h2
      obtain ⟨l'', v'', r'', h2 ⟩:= h2
      have h3: l = l''.node v'' r'' := by exact h2
      have hmin2: (l.node v r).isMinHeap := by assumption
      have hmin3: (l.node v r).isMinHeap := by assumption
      apply minHeapThenLeftAndRightAreMinHeap at hmin
      simp [leftAndRightAreMinHeap] at hmin
      have hlmin: l.isMinHeap := by grind
      have hlmin2: l.isMinHeap := by grind
      apply ih2 at hlmin
      apply hlmin at h
      grw[← h]
      apply minHeapThenRootIsMinOfChildren at hmin2
      apply rootIsMinOfChildrenLeft l r l'' r'' v v'' hmin2 at h2
      have hhl: v'' = l.heapMin := by grind [minHeapRootMin]
      have hh: v =(l.node v r).heapMin := by grind [minHeapRootMin]
      grw [← hh, ← hhl]
      exact h2
    . have h2: r.contains v' := by exact h
      apply containsIsNode at h2
      obtain ⟨l'', v'', r'', h2 ⟩:= h2
      have h3: r = l''.node v'' r'' := by exact h2
      have hmin2: (l.node v r).isMinHeap := by assumption
      have hmin3: (l.node v r).isMinHeap := by assumption
      apply minHeapThenLeftAndRightAreMinHeap at hmin
      simp [leftAndRightAreMinHeap] at hmin
      have hlmin: r.isMinHeap := by grind
      have hlmin2: r.isMinHeap := by grind
      apply ih1 at hlmin
      apply hlmin at h
      grw[← h]
      apply minHeapThenRootIsMinOfChildren at hmin2
      apply rootIsMinOfChildrenRight l r l'' r'' v v'' hmin2 at h2
      have hhl: v'' = r.heapMin := by grind [minHeapRootMin]
      have hh: v =(l.node v r).heapMin := by grind [minHeapRootMin]
      grw [← hh, ← hhl]
      exact h2

-- lemma heapifyEstablishesRootIsMinOfChildren (bt: BinaryTree ENat) (hbt: leftAndRightAreMinHeap bt): rootIsMinOfChildren (heapify bt) := by
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

-- lemma heapifyEstablishesLeftAndRigthAreMinHeap (bt: BinaryTree ENat) (hbt: leftAndRightAreMinHeap bt): leftAndRightAreMinHeap (heapify bt) := by
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

lemma heapifyPreservesMinHeap (bt: BinaryTree ENat): isMinHeap bt → bt = heapify bt := by
fun_induction heapify; all_goals expose_names; all_goals try grind
. intro hbt
  by_contra
  have hbtmin: v = heapMin (leaf.node v (rl.node rv rr)) := by grind [minHeapRootMin]
  grind[heapMin]
. intro hbt
  by_contra
  have hbtmin: v = heapMin ((ll.node lv lr).node v leaf) := by grind [minHeapRootMin]
  grind[heapMin]
. intro hbt
  have hbtmin: v = heapMin ((ll.node lv lr).node v (rl.node rv rr)) := by grind [minHeapRootMin]
  grind[heapMin]
. intro hbt
  have hbtmin: v = heapMin ((ll.node lv lr).node v (rl.node rv rr)) := by grind [minHeapRootMin]
  grind[heapMin]

lemma binTreeEqR (l r l' r': BinaryTree ENat) (v v': ENat): (node l v r) = (node l' v' r') → r = r' := by
grind only

lemma binTreeEqL (l r l' r': BinaryTree ENat) (v v': ENat): (node l v r) = (node l' v' r') → l = l' := by
grind only

-- lemma decreaseRootIsHeap (l r: BinaryTree ENat) (v v': ENat): isMinHeap (node l v r) →  v' ≤ minHeap (node l v r) → isMinHeap (node l v' r) := by sorry

lemma heapifyPreservesValues (tree r l: BinaryTree ENat) (v: ENat): tree.heapify = node r v l → contains tree v := by
grind [contains, heapifyPreservesMembers2]

lemma containsRootOrChildren (tree r l: BinaryTree ENat) (v v': ENat): tree = node r v l → contains tree v' → contains r v' ∨ contains l v' ∨ v= v' := by
grind [contains]


lemma containsRootOrChildrenLeftLeaf (tree r: BinaryTree ENat) (v v': ENat): tree = node r v leaf → contains tree v' → contains r v' ∨ v= v' := by
grind [contains]

lemma containsRightThenContainsRoot (tree l r: BinaryTree ENat) (v v': ENat): tree = node l v r → contains r v' → contains tree v' := by
grind [contains]

lemma containsLeftThenContainsRoot (tree l r: BinaryTree ENat) (v v': ENat): tree = node l v r → contains l v' → contains tree v' := by
grind [contains]

lemma heapifyEstablishesMinHeap' (bt l r: BinaryTree ENat) (v: ENat): bt = node l v r ∧  isMinHeap l ∧ isMinHeap r → isMinHeap (heapify bt) := by
fun_induction heapify generalizing l r v; all_goals expose_names
. simp [isMinHeap]
. simp [isMinHeap]
. intro ⟨hr, hminl, hminr⟩
  apply leftAndRightAreMinHeapAndRootIsMinOfChildrenToMinHeap
  have: ∃ rl' v' rr', (rl.node v_1 rr).heapify = node rl' v' rr' ∧ v' ≤ heapMin (rl.node v_1 rr) := by
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
    have hrvmin : rv = heapMin (rl.node rv rr) := by
      apply minHeapRootMin (rl.node rv rr) rl rr rv (rfl)
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
  have: ∃ ll' v' lr', (ll.node v_1 lr).heapify = node ll' v' lr' ∧ v' ≤ heapMin (ll.node v_1 lr) := by
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
    have hlvmin : lv = heapMin (ll.node lv lr) := by
      apply minHeapRootMin (ll.node lv lr) ll lr lv (rfl)
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
  have: ∃ ll' v' lr', (ll.node v_1 lr).heapify = node ll' v' lr' ∧ v' ≤ heapMin (ll.node v_1 lr) := by
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
    have hlvmin : lv = heapMin (ll.node lv lr) := by
      apply minHeapRootMin (ll.node lv lr) ll lr lv (rfl)
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
  have: ∃ rl' v' rr', (rl.node v_1 rr).heapify = node rl' v' rr' ∧ v' ≤ heapMin (rl.node v_1 rr) := by
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
    have hrvmin : rv = heapMin (rl.node rv rr) := by
      apply minHeapRootMin (rl.node rv rr) rl rr rv (rfl)
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

lemma heapifyEstablishesMinHeap (bt: BinaryTree ENat): (hbt: leftAndRightAreMinHeap bt) → isMinHeap (heapify bt) := by
cases bt
. grind[isMinHeap,leftAndRightAreMinHeap, heapify]
. grind[isMinHeap,leftAndRightAreMinHeap, heapifyEstablishesMinHeap']
