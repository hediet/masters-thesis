import tactic
import ...definitions
import ..internal_definitions
import ..Ant.main
import .eval

variable [GuardModule]
open GuardModule

@[simp]
lemma Gdt.mark_all_leaves_inactive.inactive_leaves (gdt: Gdt):
    gdt.mark_all_leaves_inactive.inactive_leaves = gdt.leaves :=
begin
    induction gdt;
    try { cases gdt_grd };
    simp [*, Gdt.leaves, Gdt.mark_all_leaves_inactive, Ant.inactive_leaves],
end

@[simp]
lemma Gdt.mark_all_leaves_inactive.critical_leaf_sets (gdt: Gdt):
    gdt.mark_all_leaves_inactive.critical_leaf_sets = ∅ :=
begin
    induction gdt;
    try { cases gdt_grd };
    simp [*, Gdt.leaves, Gdt.mark_all_leaves_inactive, Ant.critical_leaf_sets],
end

@[simp]
lemma Gdt.mark_all_leaves_inactive.leaves (gdt: Gdt):
    gdt.mark_all_leaves_inactive.leaves = gdt.leaves :=
begin
    induction gdt;
    try { cases gdt_grd };
    simp [*, Gdt.leaves, Gdt.mark_all_leaves_inactive, Ant.critical_leaf_sets],
end

@[simp]
lemma Gdt.mark_all_leaves_inactive_map_true (gdt: Gdt):
    gdt.mark_all_leaves_inactive.map (λ x, tt) = gdt.mark_all_leaves_inactive :=
begin
    induction gdt;
    try { cases gdt_grd };
    simp [*, Ant.map, Gdt.mark_all_leaves_inactive],
end

lemma Gdt.mark_all_leaves_inactive_is_reduntant_set (gdt: Gdt) (leaves: finset Leaf): gdt.mark_all_leaves_inactive.is_redundant_set leaves :=
begin
    unfold Ant.is_redundant_set,
    simp [finset.inter_subset_right],
end




lemma Gdt.mark_inactive_leaves_of_xgrd_some { xgrd: XGrd } { env env': Env } (h: xgrd_eval xgrd env = some env') (gdt: Gdt):
    (Gdt.grd (Grd.xgrd xgrd) gdt).mark_inactive_leaves env = gdt.mark_inactive_leaves env' :=
by simp [Gdt.mark_inactive_leaves, h, Gdt.mark_inactive_leaves._match_1]

lemma Gdt.mark_inactive_leaves_of_xgrd_none { xgrd: XGrd } { env: Env } (h: xgrd_eval xgrd env = none) (gdt: Gdt):
    (Gdt.grd (Grd.xgrd xgrd) gdt).mark_inactive_leaves env = gdt.mark_all_leaves_inactive :=
by simp [Gdt.mark_inactive_leaves, h, Gdt.mark_inactive_leaves._match_1]

lemma Gdt.mark_inactive_leaves_map_tt (gdt: Gdt) (env: Env):
    (gdt.mark_inactive_leaves env).map (λ x, tt) = gdt.mark_all_leaves_inactive :=
begin
    induction gdt generalizing env;
    try { cases gdt_grd };
    try { cases c: (gdt_tr1.eval env).is_match };
    try { cases c: (xgrd_eval gdt_grd env) };
    try { cases c: is_bottom gdt_grd env };
    simp [*, Gdt.leaves, Gdt.mark_inactive_leaves, Gdt.mark_all_leaves_inactive, Ant.map],
end

@[simp]
lemma Gdt.mark_inactive_leaves.leaves (gdt: Gdt) (env: Env):
    (gdt.mark_inactive_leaves env).leaves = gdt.leaves :=
begin
    induction gdt generalizing env;
    try { cases gdt_grd };
    try { cases c: (gdt_tr1.eval env).is_match };
    try { cases c: (xgrd_eval gdt_grd env) };
    try { cases c: is_bottom gdt_grd env };
    simp [*, Gdt.leaves, Gdt.mark_inactive_leaves, Ant.critical_leaf_sets],
end

lemma Gdt.mark_inactive_leaves.inactive_leaves (gdt: Gdt) (env: Env): (gdt.mark_inactive_leaves env).inactive_leaves ⊆ gdt.leaves :=
by simp only [←Gdt.mark_inactive_leaves.leaves gdt env, Ant.inactive_leaves_subset_leaves]

lemma Gdt.mark_inactive_leaves_no_match { env: Env } { gdt: Gdt } (h: gdt.eval env = Result.no_match):
    gdt.mark_inactive_leaves env = gdt.mark_all_leaves_inactive :=
begin
    induction gdt with leaf generalizing env,
    case Gdt.leaf {
        finish [Gdt.eval],
    },
    case Gdt.branch {
        simp [
            Gdt.mark_inactive_leaves, Gdt.mark_all_leaves_inactive,
            Gdt.eval_branch_no_match_iff.1 h, *
        ],
    },
    case Gdt.grd {
        cases gdt_grd with gdt_grd var,
        case Grd.xgrd {
            cases c: xgrd_eval gdt_grd env, {
                simp [Gdt.mark_inactive_leaves, Gdt.mark_all_leaves_inactive, c],
            }, {
                rw [Gdt.eval_xgrd_of_some c] at h,
                simp [Gdt.mark_inactive_leaves, Gdt.mark_all_leaves_inactive, c, gdt_ih h],
            },
        },
        case Grd.bang {
            simp [Gdt.mark_inactive_leaves, Gdt.mark_all_leaves_inactive, Gdt.eval_bang_no_match_iff.1 h, gdt_ih],
        },
    },
end
