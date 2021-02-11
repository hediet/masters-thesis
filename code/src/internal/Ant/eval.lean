import tactic
import data.finset
import ...definitions
import ..internal_definitions
import .map
import ..phi.eval
import .rhss

variable [GuardModule]
open GuardModule

lemma Ant.mark_inactive_rhss_of_map_ty_and (ant: Ant Φ) (ty: Φ) (env: Env):
    (ant.map ty.and).mark_inactive_rhss env = (ant.mark_inactive_rhss env).map (bor (!ty.eval env)) :=
by simp [Ant.mark_inactive_rhss, Ant.map_associative, function.comp, bool.bor_comm]

lemma Ant.mark_inactive_rhss_of_map_tgrd_in_some { tgrd: TGrd } { env env': Env } (h: tgrd_eval tgrd env = some env') (ant: Ant Φ):
    (ant.map (Φ.tgrd_in tgrd)).mark_inactive_rhss env = ant.mark_inactive_rhss env' :=
by simp [Ant.mark_inactive_rhss, Ant.map_associative, function.comp, Φ_eval_tgrd_some h]

lemma Ant.mark_inactive_rhss_of_map_tgrd_in_none { tgrd: TGrd } { env: Env } (h: tgrd_eval tgrd env = none) (ant: Ant Φ):
    (ant.map (Φ.tgrd_in tgrd)).mark_inactive_rhss env = ant.map (λ r, tt) :=
by simp [Ant.mark_inactive_rhss, Ant.map_associative, function.comp, Φ_eval_tgrd_none h]

lemma Ant.mark_inactive_rhss_of_diverge (ty: Φ) (tr: Ant Φ) (env: Env):
    (Ant.diverge ty tr).mark_inactive_rhss env = (Ant.diverge (!ty.eval env) (tr.mark_inactive_rhss env)) :=
by refl


@[simp]
lemma Ant.mark_inactive_rhss.branch (ant1 ant2: Ant Φ) (env: Env):
    (ant1.branch ant2).mark_inactive_rhss env = (ant1.mark_inactive_rhss env).branch (ant2.mark_inactive_rhss env) :=
by simp only [Ant.map, Ant.mark_inactive_rhss, eq_self_iff_true, and_self]

lemma Ant.mark_inactive_rhss_map_not_eq_of_eval_rhss (ant: Ant Φ) (env: Env): (ant.mark_inactive_rhss env) = (ant.eval_rhss env).map (λ a, !a) :=
by simp only [Ant.mark_inactive_rhss, Ant.eval_rhss, Ant.map_associative, function.comp, bnot_bnot]

lemma Ant.mark_inactive_rhss_eq_of_eval_rhss_eq { ant1 ant2: Ant Φ } (h: ant1.eval_rhss = ant2.eval_rhss):
    ant1.mark_inactive_rhss = ant2.mark_inactive_rhss :=
by ext env; simp [Ant.mark_inactive_rhss_map_not_eq_of_eval_rhss, h]

@[simp]
lemma Ant.mark_inactive_rhss_disjoint_rhss_iff { ant: Ant Φ } { env: Env }:
    (ant.mark_inactive_rhss env).disjoint_rhss ↔ ant.disjoint_rhss :=
by simp [Ant.mark_inactive_rhss]

@[simp]
lemma Ant.mark_inactive_rhss_branch (ant1 ant2: Ant Φ) (env: Env): (ant1.branch ant2).mark_inactive_rhss env = ((ant1.mark_inactive_rhss env).branch (ant2.mark_inactive_rhss env)) :=
by refl

lemma Ant.inactive_rhss_subset_rhss { a: Ant bool } : a.inactive_rhss ⊆ a.rhss :=
begin
    induction a,
    cases a_a,
    all_goals {
        simp [Ant.inactive_rhss, finset.union_subset_union, *],
    },
end
