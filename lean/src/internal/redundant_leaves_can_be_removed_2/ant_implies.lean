import tactic
import ...definitions
import ..helper_defs
import data.finset
import ..utils
import data.list
import data.bool
import ..leaves_theory

variable [GuardModule]
open GuardModule

def Ant.implies: Ant bool → Ant bool → Prop
| (Ant.branch a_tr1 a_tr2) (Ant.branch b_tr1 b_tr2) := a_tr1.implies b_tr1 ∧ a_tr2.implies b_tr2
| (Ant.diverge a a_tr) (Ant.diverge b b_tr) := (a → b) ∧ a_tr.implies b_tr
| (Ant.leaf a a_leaf) (Ant.leaf b b_leaf) := (a → b) ∧ a_leaf = b_leaf
| _ _ := false

inductive Ant.implies2: Ant bool → Ant bool → Prop
| leaf { a b: bool } { leaf } (h: a → b):
    Ant.implies2 (Ant.leaf a leaf) (Ant.leaf b leaf)
| branch { a_tr1 a_tr2 b_tr1 b_tr2 } (h1: Ant.implies2 a_tr1 b_tr1) (h2: Ant.implies2 a_tr2 b_tr2):
    Ant.implies2 (Ant.branch a_tr1 a_tr2) (Ant.branch b_tr1 b_tr2)
| diverge { a b: bool } { a_tr b_tr } (h1: Ant.implies2 a_tr b_tr) (h2: a → b):
    Ant.implies2 (Ant.diverge a a_tr) (Ant.diverge b b_tr)

notation a ⇒ b := Ant.implies2 a b

def Ant.implies_equal_structure { a b: Ant bool } (h: a ⇒ b):
    a.map (λ x, false) = b.map (λ x, false) :=
begin
    induction h;
    simp [Ant.map, *],
end

def Ant.implies_same_leaves { a b: Ant bool } (h: a ⇒ b): a.leaves = b.leaves :=
begin
    have := congr_arg Ant.leaves (Ant.implies_equal_structure h),
    finish [map_leaves_id],
end
