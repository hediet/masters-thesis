import tactic
import ...definitions
import ..internal_definitions

variable [GuardModule]
open GuardModule

lemma Gdt.eval_branch_right { gdt1: Gdt } { gdt2: Gdt } { env: Env } (h: gdt1.eval env = Result.no_match):
    (gdt1.branch gdt2).eval env = gdt2.eval env :=
by cases c: gdt2.eval env; finish [Gdt.eval]

lemma Gdt.eval_branch_left { gdt1: Gdt } { gdt2: Gdt } { env: Env } (h: gdt1.eval env ≠ Result.no_match ∨ gdt2.eval env = Result.no_match):
    (gdt1.branch gdt2).eval env = gdt1.eval env :=
by cases c: gdt1.eval env; finish [Gdt.eval]

@[simp]
lemma Gdt.eval_branch_no_match_iff { gdt1: Gdt } { gdt2: Gdt } { env: Env }:
    (gdt1.branch gdt2).eval env = Result.no_match ↔ gdt1.eval env = Result.no_match ∧ gdt2.eval env = Result.no_match :=
begin
    cases c1: gdt1.eval env;
    cases c2: gdt2.eval env;
    finish [Gdt.eval, Gdt.eval._match_2, Gdt.eval._match_1],
end

@[simp]
lemma Gdt.eval_branch_diverge_iff { gdt1: Gdt } { gdt2: Gdt } { env: Env }:
    (gdt1.branch gdt2).eval env = Result.diverged
    ↔ gdt1.eval env = Result.diverged
        ∨ (gdt1.eval env = Result.no_match ∧ gdt2.eval env = Result.diverged) :=
begin
    cases c1: gdt1.eval env;
    cases c2: gdt2.eval env;
    finish [Gdt.eval, Gdt.eval._match_2, Gdt.eval._match_1],
end

@[simp]
lemma Gdt.eval_branch_rhs_iff { gdt1: Gdt } { gdt2: Gdt } { env: Env } { rhs: Rhs }:
    (gdt1.branch gdt2).eval env = Result.rhs rhs
    ↔ gdt1.eval env = Result.rhs rhs
        ∨ (gdt1.eval env = Result.no_match ∧ gdt2.eval env = Result.rhs rhs) :=
begin
    cases c1: gdt1.eval env;
    cases c2: gdt2.eval env;
    finish [Gdt.eval, Gdt.eval._match_2, Gdt.eval._match_1],
end

@[simp]
lemma Gdt.eval_rhs { rhs: Rhs } { env: Env }: (Gdt.rhs rhs).eval env = Result.rhs rhs :=
by simp [Gdt.eval]

lemma Gdt.eval_xgrd_of_some { xgrd: XGrd } { tr: Gdt } { env env': Env }
    (h: xgrd_eval xgrd env = some env'):
    (Gdt.grd (Grd.xgrd xgrd) tr).eval env = tr.eval env' :=
by simp [Gdt.eval, h]

lemma Gdt.eval_xgrd_of_none { xgrd: XGrd } { tr: Gdt } { env: Env }
    (h: xgrd_eval xgrd env = none):
    (Gdt.grd (Grd.xgrd xgrd) tr).eval env = Result.no_match :=
by simp [Gdt.eval, h]

lemma Gdt.eval_bang_of_bottom { var: Var } { tr: Gdt } { env: Env }
    (h: is_bottom var env = tt):
    (Gdt.grd (Grd.bang var) tr).eval env = Result.diverged :=
by simp [Gdt.eval, h]

lemma Gdt.eval_bang_of_not_bottom { var: Var } { tr: Gdt } { env: Env }
    (h: is_bottom var env = ff):
    (Gdt.grd (Grd.bang var) tr).eval env = tr.eval env :=
by simp [Gdt.eval, h]

@[simp]
lemma Gdt.eval_bang_no_match_iff { var: Var } { tr: Gdt } { env: Env }:
    (Gdt.grd (Grd.bang var) tr).eval env = Result.no_match ↔ is_bottom var env = ff ∧ tr.eval env = Result.no_match :=
by cases c: is_bottom var env; simp [Gdt.eval, c]

lemma Gdt.eval_branch_replace_right_env { gdt₁ gdt₂ gdt₂': Gdt } { env: Env }
    (h: gdt₂.eval env = gdt₂'.eval env ∨ gdt₁.eval env ≠ Result.no_match):
    (gdt₁.branch gdt₂).eval env = (gdt₁.branch gdt₂').eval env :=
by by_cases x: gdt₁.eval env = Result.no_match; finish [Gdt.eval_branch_left, Gdt.eval_branch_right, x]


lemma Gdt.rhs_mem_rhss_of_eval_rhs { gdt: Gdt } { env: Env } { rhs: Rhs } (h: gdt.eval env = Result.rhs rhs): rhs ∈ gdt.rhss :=
begin
    induction gdt with rhs generalizing env,
    case Gdt.rhs {
        finish [Gdt.rhss, Gdt.eval],
    },
    case Gdt.grd {
        cases gdt_grd,
        case Grd.xgrd {
            cases c: xgrd_eval gdt_grd env,
            { finish [Gdt.rhss, Gdt.eval_xgrd_of_none c, Gdt.eval], },
            { finish [Gdt.rhss, Gdt.eval_xgrd_of_some c, Gdt.eval], },
        },
        case Grd.bang {
            cases c: is_bottom gdt_grd env,
            { finish [Gdt.rhss, Gdt.eval_bang_of_not_bottom c], },
            { finish [Gdt.rhss, Gdt.eval_bang_of_bottom c], },
        }
    },
    case Gdt.branch {
        by_cases c: gdt_tr1.eval env = Result.no_match;
        finish [Gdt.rhss, Gdt.eval_branch_rhs_iff],
    },
end
