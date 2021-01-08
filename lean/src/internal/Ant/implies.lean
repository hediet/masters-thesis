import tactic
import data.finset
import ...definitions
import ..internal_definitions
import .leaves
import ..tactics
import ..utils
import .map
import ..U

variable [GuardModule]
open GuardModule

@[trans] lemma Ant.implies_trans (a b c : Ant bool) (h1: a ⟶ b) (h2: b ⟶ c): a ⟶ c :=
begin
    induction h1 generalizing c;
    cases h2,
    {
        refine Ant.implies.leaf _,
        tauto,
    }, {
        refine Ant.implies.branch _ _,
        tauto,
        tauto,
    }, {
        refine Ant.implies.diverge _ _,
        tauto,
        tauto,
    },
end

@[refl] lemma Ant.implies_refl (a : Ant bool) : a ⟶ a :=
by induction a; simp [Ant.implies.leaf, Ant.implies.branch, Ant.implies.diverge, *]

lemma Ant.implies_equal_structure { a b: Ant bool } (h: a ⟶ b):
    a.map (λ x, false) = b.map (λ x, false) :=
begin
    induction h;
    simp [Ant.map, *],
end

lemma Ant.implies_same_leaves { a b: Ant bool } (h: a ⟶ b): a.leaves = b.leaves :=
begin
    have := congr_arg Ant.leaves (Ant.implies_equal_structure h),
    finish [Ant.map_leaves],
end
