import tactic
import ..definitions
import data.finset

variable [GuardModule]
open GuardModule

def Result.is_match : Result → bool
| Result.no_match := ff
| _ := tt

-- ######################## Gdt ########################

-- Simpler definition of 𝒰 that does not need an accumulator
def U : Gdt → Φ
| (Gdt.leaf _) := Φ.false
| (Gdt.branch tr1 tr2) := (U tr1).and (U tr2)
| (Gdt.grd (Grd.bang var) tree) := ((Φ.var_is_not_bottom var).and (U tree))
| (Gdt.grd (Grd.xgrd grd) tree) :=
                (Φ.not_xgrd grd)
            .or
                (Φ.xgrd_in grd (U tree))

def Gdt.mark_all_leaves_inactive: Gdt → Ant bool
| (Gdt.leaf leaf) := Ant.leaf tt leaf 
| (Gdt.branch tr1 tr2) := Ant.branch tr1.mark_all_leaves_inactive tr2.mark_all_leaves_inactive
| (Gdt.grd (Grd.xgrd _) tr) := tr.mark_all_leaves_inactive
| (Gdt.grd (Grd.bang _) tr) := Ant.diverge tt tr.mark_all_leaves_inactive

def Gdt.mark_inactive_leaves : Gdt → Env → Ant bool
| (Gdt.leaf leaf) env := Ant.leaf ff leaf 
| (Gdt.branch tr1 tr2) env :=
    Ant.branch (tr1.mark_inactive_leaves env) (
        if (tr1.eval env).is_match then
            (tr2.mark_all_leaves_inactive)
        else
            (tr2.mark_inactive_leaves env)
    )
| (Gdt.grd (Grd.xgrd grd) tr) env :=
    match xgrd_eval grd env with
    | none := tr.mark_all_leaves_inactive
    | some env' := tr.mark_inactive_leaves env'
    end
| (Gdt.grd (Grd.bang var) tr) env :=
    if is_bottom var env
    then Ant.diverge ff (tr.mark_all_leaves_inactive)
    else Ant.diverge tt (tr.mark_inactive_leaves env)

-- ######################## Ant ########################

def Ant.leaves_list { α: Type }: Ant α → list Leaf
| (Ant.leaf a leaf) := [ leaf ]
| (Ant.branch tr1 tr2) := Ant.leaves_list tr1 ++ Ant.leaves_list tr2
| (Ant.diverge a tr) := Ant.leaves_list tr

def Ant.leaves { α: Type } (ant: Ant α): finset Leaf := ant.leaves_list.to_finset

def Ant.disjoint_leaves { α: Type } : Ant α → Prop
| (Ant.leaf _ leaf) := true
| (Ant.branch tr1 tr2) := tr1.disjoint_leaves ∧ tr2.disjoint_leaves ∧ disjoint tr1.leaves tr2.leaves
| (Ant.diverge _ tr) := tr.disjoint_leaves

def Ant.map { α β: Type } : (α → β) → Ant α → Ant β
| f (Ant.leaf a leaf) := Ant.leaf (f a) leaf
| f (Ant.branch tr1 tr2) := (Ant.branch (tr1.map f) (tr2.map f))
| f (Ant.diverge a tr) := (Ant.diverge (f a) (tr.map f))
-- TODO: functor implementieren? f <$> ant

def Ant.map_option { α β: Type } : (α → β) → option (Ant α) → option (Ant β)
| f (some ant) := some (ant.map f)
| f none := none
-- TODO: fmap?

def Ant.eval_leaves (ant: Ant Φ) (env: Env) := ant.map (λ ty, ty.eval env)

def Ant.mark_inactive_leaves (ant: Ant Φ) (env: Env) := ant.map (λ ty, !(ty.eval env))

def Ant.inactive_leaves : Ant bool → finset Leaf
| (Ant.leaf inactive n) := if inactive then { n } else ∅
| (Ant.diverge inactive tr) := tr.inactive_leaves
| (Ant.branch tr1 tr2) := tr1.inactive_leaves ∪ tr2.inactive_leaves

inductive Ant.implies: Ant bool → Ant bool → Prop
| leaf { a b: bool } { leaf } (h: a → b):
    Ant.implies (Ant.leaf a leaf) (Ant.leaf b leaf)
| branch { a_tr1 a_tr2 b_tr1 b_tr2 } (h1: Ant.implies a_tr1 b_tr1) (h2: Ant.implies a_tr2 b_tr2):
    Ant.implies (Ant.branch a_tr1 a_tr2) (Ant.branch b_tr1 b_tr2)
| diverge { a b: bool } { a_tr b_tr } (h1: Ant.implies a_tr b_tr) (h2: a → b):
    Ant.implies (Ant.diverge a a_tr) (Ant.diverge b b_tr)

infix `⟶`: 50 := Ant.implies

def Ant.critical_leaf_sets : Ant bool → finset (finset Leaf)
| (Ant.leaf inactive n) := ∅
| (Ant.diverge inactive tr) := tr.critical_leaf_sets ∪ if inactive
    then ∅
    else { tr.leaves }
| (Ant.branch tr1 tr2) := tr1.critical_leaf_sets ∪ tr2.critical_leaf_sets

def Ant.is_redundant_set (a: Ant bool) (leaves: finset Leaf) :=
    leaves ∩ a.leaves ⊆ a.inactive_leaves
    ∧ ∀ c ∈ a.critical_leaf_sets, ∃ l ∈ c, l ∉ leaves
-- TODO: rcases

-- leaves.redundant_in ant
-- ant.is_redundant_set leaves

-- This is a simpler definition of 𝒜 that is semantically equivalent.
def A : Gdt → Ant Φ
| (Gdt.leaf leaf) := Ant.leaf Φ.true leaf
| (Gdt.branch tr1 tr2) := Ant.branch (A tr1) $ (A tr2).map ((U tr1).and)
| (Gdt.grd (Grd.bang var) tr) := Ant.diverge (Φ.var_is_bottom var) $ (A tr).map ((Φ.var_is_not_bottom var).and)
| (Gdt.grd (Grd.xgrd grd) tr) := (A tr).map (Φ.xgrd_in grd)

-- ######################## R ########################

-- (accessible, inaccessible, redundant)
structure LeafPartition := mk :: (acc : list Leaf) (inacc : list Leaf) (red : list Leaf)

def LeafPartition.leaves (p: LeafPartition) : list Leaf := p.acc ++ p.inacc ++ p.red

def LeafPartition.to_triple (p: LeafPartition): (list Leaf × list Leaf × list Leaf) :=
    (p.acc, p.inacc, p.red)

/-
    This definition is much easier to use than ℛ, but almost equal to ℛ.
    * Associativity of `Ant.map` can be utilized.
    * LeafPartition is much easier to use than triples.
    * Ant.branch has no match which would require a case distinction.
    * This definition can handle any `Ant bool`.
-/
def R : Ant bool → LeafPartition
| (Ant.leaf can_prove_empty n) := if can_prove_empty then ⟨ [], [], [n] ⟩ else ⟨ [n], [], [] ⟩
| (Ant.diverge can_prove_empty tr) := 
    match R tr, can_prove_empty with
    | ⟨ [], [], m :: ms ⟩, ff := ⟨ [], [m], ms ⟩
    | r, _ := r
    end
| (Ant.branch tr1 tr2) :=
    let r1 := R tr1, r2 := R tr2 in
        ⟨ r1.acc ++ r2.acc, r1.inacc ++ r2.inacc, r1.red ++ r2.red ⟩
