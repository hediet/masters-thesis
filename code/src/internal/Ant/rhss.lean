import tactic
import data.finset
import ...definitions
import ..internal_definitions
import ..utils
import ..tactics
import .map

variable [GuardModule]
open GuardModule

lemma Ant.rhss_list.nodup { α: Type } { ant: Ant α } (ant_disjoint: ant.disjoint_rhss): ant.rhss_list.nodup :=
by induction_ant_disjoint ant from ant_disjoint;
    finish [Ant.rhss_list, Ant.rhss, list.nodup_append, list_to_finset_disjoint_iff_list_disjoint]

@[simp]
lemma Ant.rhss_branch { α: Type } { ant1 ant2: Ant α }: (ant1.branch ant2).rhss = ant1.rhss ∪ ant2.rhss :=
by simp [Ant.rhss, Ant.rhss_list]

@[simp]
lemma Ant.rhss_diverge { α: Type } { a: α } { tr: Ant α }: (Ant.diverge a tr).rhss = tr.rhss :=
by simp [Ant.rhss, Ant.rhss_list]

@[simp]
lemma Ant.rhss_rhs { α: Type } { a: α } { rhs: Rhs }: (Ant.rhs a rhs).rhss = { rhs } :=
by simp [Ant.rhss, Ant.rhss_list]

lemma Ant.rhss_non_empty { α: Type } (ant: Ant α) : ∃ l, l ∈ ant.rhss :=
by induction ant; finish

lemma Ant.critical_rhs_set_elements { ant: Ant bool } { e: finset Rhs } (h: e ∈ ant.critical_rhs_sets):
    e ⊆ ant.rhss :=
begin
    induction ant;
    rw Ant.critical_rhs_sets at h,
    case Ant.rhs { finish, },
    case Ant.branch {
        simp only [finset.mem_union] at h,
        cases h;
        simp [subset_right_union, subset_left_union, *],
    },
    case Ant.diverge {
        simp only [finset.mem_union] at h,
        cases h;
        try {
            cases ant_a;
            finish,
        },
    },
end

@[simp]
lemma ant_mark_inactive_rhss { ant: Ant Φ } { env: Env }: (ant.mark_inactive_rhss env).rhss = ant.rhss :=
by simp [Ant.mark_inactive_rhss]


@[simp]
lemma Ant.disjoint_rhss_of_map { α β: Type } { f: α → β } { ant: Ant α }: (ant.map f).disjoint_rhss ↔ ant.disjoint_rhss :=
by induction ant; { simp only [Ant.map, Ant.disjoint_rhss, *, Ant.map_rhss], }

@[simp]
lemma Ant.disjoint_rhss_of_mark_inactive_rhss { ant: Ant Φ } { env: Env }:
    (ant.mark_inactive_rhss env).disjoint_rhss ↔ ant.disjoint_rhss :=
by simp [Ant.mark_inactive_rhss]

lemma Ant.disjoint_rhss_of_mark_inactive_rhss_eq { ant1 ant2: Ant Φ } { env: Env } (h: ant1.mark_inactive_rhss env = ant2.mark_inactive_rhss env):
    ant1.disjoint_rhss ↔ ant2.disjoint_rhss :=
begin
    have : (ant1.mark_inactive_rhss env).disjoint_rhss ↔ (ant2.mark_inactive_rhss env).disjoint_rhss := by rw h,
    simp at this,
    exact this,
end
