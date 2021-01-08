import tactic
import data.finset
import ...definitions
import ..internal_definitions
import ..utils
import ..tactics
import .map

variable [GuardModule]
open GuardModule

lemma Ant.leaves_list.nodup { α: Type } { ant: Ant α } (ant_disjoint: ant.disjoint_leaves): ant.leaves_list.nodup :=
by induction_ant_disjoint ant from ant_disjoint;
    finish [Ant.leaves_list, Ant.leaves, list.nodup_append, list_to_finset_disjoint_iff_list_disjoint]

@[simp]
lemma Ant.leaves_branch { α: Type } { ant1 ant2: Ant α }: (ant1.branch ant2).leaves = ant1.leaves ∪ ant2.leaves :=
by simp [Ant.leaves, Ant.leaves_list]

@[simp]
lemma Ant.leaves_diverge { α: Type } { a: α } { tr: Ant α }: (Ant.diverge a tr).leaves = tr.leaves :=
by simp [Ant.leaves, Ant.leaves_list]

@[simp]
lemma Ant.leaves_leaf { α: Type } { a: α } { leaf: Leaf }: (Ant.leaf a leaf).leaves = { leaf } :=
by simp [Ant.leaves, Ant.leaves_list]

lemma Ant.leaves_non_empty { α: Type } (ant: Ant α) : ∃ l, l ∈ ant.leaves :=
by induction ant; finish

lemma Ant.critical_leaf_set_elements { ant: Ant bool } { e: finset Leaf } (h: e ∈ ant.critical_leaf_sets):
    e ⊆ ant.leaves :=
begin
    induction ant;
    rw Ant.critical_leaf_sets at h,
    case Ant.leaf {
        finish,
    },
    case Ant.branch {
        simp at h,
        cases h;
        simp [subset_right_union, subset_left_union, *],
    },
    case Ant.diverge {
        simp at h,
        cases h;
        try {
            cases ant_a;
            finish,
        },
    },
end

@[simp]
lemma ant_mark_inactive_leaves { ant: Ant Φ } { env: Env }: (ant.mark_inactive_leaves env).leaves = ant.leaves :=
begin
    unfold Ant.mark_inactive_leaves,
    simp,
end


@[simp]
lemma Ant.disjoint_leaves_of_map { α β: Type } { f: α → β } { ant: Ant α }: (ant.map f).disjoint_leaves ↔ ant.disjoint_leaves :=
by induction ant; { simp only [Ant.map, Ant.disjoint_leaves, *, Ant.map_leaves], }

@[simp]
lemma Ant.disjoint_leaves_of_mark_inactive_leaves { ant: Ant Φ } { env: Env }:
    (ant.mark_inactive_leaves env).disjoint_leaves ↔ ant.disjoint_leaves :=
by simp [Ant.mark_inactive_leaves]

lemma Ant.disjoint_leaves_of_mark_inactive_leaves_eq { ant1 ant2: Ant Φ } { env: Env } (h: ant1.mark_inactive_leaves env = ant2.mark_inactive_leaves env):
    ant1.disjoint_leaves ↔ ant2.disjoint_leaves :=
begin
    have : (ant1.mark_inactive_leaves env).disjoint_leaves ↔ (ant2.mark_inactive_leaves env).disjoint_leaves := by rw h,
    simp at this,
    exact this,
end
