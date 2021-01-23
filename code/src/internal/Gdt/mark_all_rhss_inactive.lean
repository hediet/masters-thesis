import tactic
import ...definitions
import ..internal_definitions
import ..Ant.main
import .eval

variable [GuardModule]
open GuardModule

@[simp]
lemma Gdt.mark_all_rhss_inactive.inactive_rhss (gdt: Gdt):
    gdt.mark_all_rhss_inactive.inactive_rhss = gdt.rhss :=
begin
    induction gdt;
    try { cases gdt_grd };
    simp [*, Gdt.rhss, Gdt.mark_all_rhss_inactive, Ant.inactive_rhss],
end

@[simp]
lemma Gdt.mark_all_rhss_inactive.critical_rhs_sets (gdt: Gdt):
    gdt.mark_all_rhss_inactive.critical_rhs_sets = ∅ :=
begin
    induction gdt;
    try { cases gdt_grd };
    simp [*, Gdt.rhss, Gdt.mark_all_rhss_inactive, Ant.critical_rhs_sets],
end

@[simp]
lemma Gdt.mark_all_rhss_inactive.rhss (gdt: Gdt):
    gdt.mark_all_rhss_inactive.rhss = gdt.rhss :=
begin
    induction gdt;
    try { cases gdt_grd };
    simp [*, Gdt.rhss, Gdt.mark_all_rhss_inactive, Ant.critical_rhs_sets],
end

@[simp]
lemma Gdt.mark_all_rhss_inactive_map_true (gdt: Gdt):
    gdt.mark_all_rhss_inactive.map (λ x, tt) = gdt.mark_all_rhss_inactive :=
begin
    induction gdt;
    try { cases gdt_grd };
    simp [*, Ant.map, Gdt.mark_all_rhss_inactive],
end

lemma Gdt.mark_all_rhss_inactive_is_reduntant_set (gdt: Gdt) (rhss: finset Rhs): gdt.mark_all_rhss_inactive.is_redundant_set rhss :=
by simp [Ant.is_redundant_set, finset.inter_subset_right]


lemma Gdt.mark_inactive_rhss_of_xgrd_some { xgrd: XGrd } { env env': Env } (h: xgrd_eval xgrd env = some env') (gdt: Gdt):
    (Gdt.grd (Grd.xgrd xgrd) gdt).mark_inactive_rhss env = gdt.mark_inactive_rhss env' :=
by simp [Gdt.mark_inactive_rhss, h, Gdt.mark_inactive_rhss._match_1]

lemma Gdt.mark_inactive_rhss_of_xgrd_none { xgrd: XGrd } { env: Env } (h: xgrd_eval xgrd env = none) (gdt: Gdt):
    (Gdt.grd (Grd.xgrd xgrd) gdt).mark_inactive_rhss env = gdt.mark_all_rhss_inactive :=
by simp [Gdt.mark_inactive_rhss, h, Gdt.mark_inactive_rhss._match_1]

lemma Gdt.mark_inactive_rhss_map_tt (gdt: Gdt) (env: Env):
    (gdt.mark_inactive_rhss env).map (λ x, tt) = gdt.mark_all_rhss_inactive :=
begin
    induction gdt generalizing env;
    try { cases gdt_grd };
    try { cases c: (gdt_tr1.eval env).is_match };
    try { cases c: (xgrd_eval gdt_grd env) };
    try { cases c: is_bottom gdt_grd env };
    simp [*, Gdt.rhss, Gdt.mark_inactive_rhss, Gdt.mark_all_rhss_inactive, Ant.map],
end

@[simp]
lemma Gdt.mark_inactive_rhss.rhss (gdt: Gdt) (env: Env):
    (gdt.mark_inactive_rhss env).rhss = gdt.rhss :=
begin
    induction gdt generalizing env;
    try { cases gdt_grd };
    try { cases c: (gdt_tr1.eval env).is_match };
    try { cases c: (xgrd_eval gdt_grd env) };
    try { cases c: is_bottom gdt_grd env };
    simp [*, Gdt.rhss, Gdt.mark_inactive_rhss, Ant.critical_rhs_sets],
end

lemma Gdt.mark_inactive_rhss.inactive_rhss (gdt: Gdt) (env: Env): (gdt.mark_inactive_rhss env).inactive_rhss ⊆ gdt.rhss :=
by simp only [←Gdt.mark_inactive_rhss.rhss gdt env, Ant.inactive_rhss_subset_rhss]

lemma Gdt.mark_inactive_rhss_no_match { env: Env } { gdt: Gdt } (h: gdt.eval env = Result.no_match):
    gdt.mark_inactive_rhss env = gdt.mark_all_rhss_inactive :=
begin
    induction gdt with rhs generalizing env,
    case Gdt.rhs { finish [Gdt.eval], },
    case Gdt.branch {
        simp [
            Gdt.mark_inactive_rhss, Gdt.mark_all_rhss_inactive,
            Gdt.eval_branch_no_match_iff.1 h, *
        ],
    },
    case Gdt.grd {
        cases gdt_grd with gdt_grd var,
        case Grd.xgrd {
            cases c: xgrd_eval gdt_grd env, {
                simp [Gdt.mark_inactive_rhss, Gdt.mark_all_rhss_inactive, c],
            }, {
                rw [Gdt.eval_xgrd_of_some c] at h,
                simp [Gdt.mark_inactive_rhss, Gdt.mark_all_rhss_inactive, c, gdt_ih h],
            },
        },
        case Grd.bang {
            simp [Gdt.mark_inactive_rhss, Gdt.mark_all_rhss_inactive, Gdt.eval_bang_no_match_iff.1 h, gdt_ih],
        },
    },
end
