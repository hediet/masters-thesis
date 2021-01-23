import tactic
import data.finset
import ..internal_definitions
import .rhss
import .map

variable [GuardModule]
open GuardModule

@[trans] lemma Ant.implies_trans (a b c : Ant bool) (h1: a ⟶ b) (h2: b ⟶ c): a ⟶ c :=
begin
    induction h1 generalizing c;
    cases h2,
    { refine Ant.implies.rhs _; tauto, },
    { refine Ant.implies.branch _ _; tauto, },
    { refine Ant.implies.diverge _ _; tauto, },
end

@[refl] lemma Ant.implies_refl (a : Ant bool) : a ⟶ a :=
by induction a; simp [Ant.implies.rhs, Ant.implies.branch, Ant.implies.diverge, *]

lemma Ant.implies_equal_structure { a b: Ant bool } (h: a ⟶ b):
    a.map (λ x, false) = b.map (λ x, false) :=
by induction h; simp [Ant.map, *]

lemma Ant.implies_same_rhss { a b: Ant bool } (h: a ⟶ b): a.rhss = b.rhss :=
begin
    have := congr_arg Ant.rhss (Ant.implies_equal_structure h),
    finish [Ant.map_rhss],
end
