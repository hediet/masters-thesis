import tactic
import data.finset
import ...definitions
import ..internal_definitions
import .map
import ..phi.eval
import .leaves

variable [GuardModule]
open GuardModule

lemma Ant.mark_inactive_leaves_of_map_ty_and (ant: Ant Φ) (ty: Φ) (env: Env):
    (ant.map ty.and).mark_inactive_leaves env = (ant.mark_inactive_leaves env).map (bor (!ty.eval env)) :=
by simp [Ant.mark_inactive_leaves, Ant.map_associative, function.comp, bool.bor_comm]

lemma Ant.mark_inactive_leaves_of_map_xgrd_in_some { xgrd: XGrd } { env env': Env } (h: xgrd_eval xgrd env = some env') (ant: Ant Φ):
    (ant.map (Φ.xgrd_in xgrd)).mark_inactive_leaves env = ant.mark_inactive_leaves env' :=
by simp [Ant.mark_inactive_leaves, Ant.map_associative, function.comp, Φ_eval_xgrd_some h]

lemma Ant.mark_inactive_leaves_of_map_xgrd_in_none { xgrd: XGrd } { env: Env } (h: xgrd_eval xgrd env = none) (ant: Ant Φ):
    (ant.map (Φ.xgrd_in xgrd)).mark_inactive_leaves env = ant.map (λ r, tt) :=
by simp [Ant.mark_inactive_leaves, Ant.map_associative, function.comp, Φ_eval_xgrd_none h]

lemma Ant.mark_inactive_leaves_of_diverge (ty: Φ) (tr: Ant Φ) (env: Env):
    (Ant.diverge ty tr).mark_inactive_leaves env = (Ant.diverge (!ty.eval env) (tr.mark_inactive_leaves env)) :=
by refl


@[simp]
lemma Ant.mark_inactive_leaves.branch (ant1 ant2: Ant Φ) (env: Env):
    (ant1.branch ant2).mark_inactive_leaves env = (ant1.mark_inactive_leaves env).branch (ant2.mark_inactive_leaves env) :=
by simp only [Ant.map, Ant.mark_inactive_leaves, eq_self_iff_true, and_self]

lemma Ant.mark_inactive_leaves_map_not_eq_of_eval_leaves (ant: Ant Φ) (env: Env): (ant.mark_inactive_leaves env) = (ant.eval_leaves env).map (λ a, !a) :=
by simp only [Ant.mark_inactive_leaves, Ant.eval_leaves, Ant.map_associative, function.comp, bnot_bnot]

lemma Ant.mark_inactive_leaves_eq_of_eval_leaves_eq { ant1 ant2: Ant Φ } (h: ant1.eval_leaves = ant2.eval_leaves):
    ant1.mark_inactive_leaves = ant2.mark_inactive_leaves :=
by ext env; simp [Ant.mark_inactive_leaves_map_not_eq_of_eval_leaves, h]

@[simp]
lemma Ant.mark_inactive_leaves_disjoint_leaves_iff { ant: Ant Φ } { env: Env }:
    (ant.mark_inactive_leaves env).disjoint_leaves ↔ ant.disjoint_leaves :=
by simp [Ant.mark_inactive_leaves]

@[simp]
lemma Ant.mark_inactive_leaves_branch (ant1 ant2: Ant Φ) (env: Env): (ant1.branch ant2).mark_inactive_leaves env = ((ant1.mark_inactive_leaves env).branch (ant2.mark_inactive_leaves env)) :=
by refl

lemma Ant.inactive_leaves_subset_leaves { a: Ant bool } : a.inactive_leaves ⊆ a.leaves :=
begin
    induction a,
    cases a_a,
    all_goals {
        simp [Ant.inactive_leaves, finset.union_subset_union, *],
    },
end
