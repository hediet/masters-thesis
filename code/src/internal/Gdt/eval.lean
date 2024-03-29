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
    finish [Gdt.eval, Gdt.eval._match_1],
end

@[simp]
lemma Gdt.eval_branch_diverge_iff { gdt1: Gdt } { gdt2: Gdt } { env: Env }:
    (gdt1.branch gdt2).eval env = Result.diverged
    ↔ gdt1.eval env = Result.diverged
        ∨ (gdt1.eval env = Result.no_match ∧ gdt2.eval env = Result.diverged) :=
begin
    cases c1: gdt1.eval env;
    cases c2: gdt2.eval env;
    finish [Gdt.eval, Gdt.eval._match_1],
end

@[simp]
lemma Gdt.eval_branch_rhs_iff { gdt1: Gdt } { gdt2: Gdt } { env: Env } { rhs: Rhs }:
    (gdt1.branch gdt2).eval env = Result.value rhs
    ↔ gdt1.eval env = Result.value rhs
        ∨ (gdt1.eval env = Result.no_match ∧ gdt2.eval env = Result.value rhs) :=
begin
    cases c1: gdt1.eval env;
    cases c2: gdt2.eval env;
    finish [Gdt.eval, Gdt.eval._match_1],
end

@[simp]
lemma Gdt.eval_rhs { rhs: Rhs } { env: Env }: (Gdt.rhs rhs).eval env = Result.value rhs :=
by simp [Gdt.eval]

lemma Gdt.eval_tgrd_of_some { tgrd: TGrd } { tr: Gdt } { env env': Env }
    (h: tgrd_eval tgrd env = some env'):
    (Gdt.grd (Grd.tgrd tgrd) tr).eval env = tr.eval env' :=
by simp [Gdt.eval, Grd.eval, Result.bind, h]

lemma Gdt.eval_tgrd_of_none { tgrd: TGrd } { tr: Gdt } { env: Env }
    (h: tgrd_eval tgrd env = none):
    (Gdt.grd (Grd.tgrd tgrd) tr).eval env = Result.no_match :=
by simp [Gdt.eval, Grd.eval, Result.bind, h]

lemma Gdt.eval_bang_of_bottom { var: Var } { tr: Gdt } { env: Env }
    (h: is_bottom var env = tt):
    (Gdt.grd (Grd.bang var) tr).eval env = Result.diverged :=
by simp [Gdt.eval, Grd.eval, Result.bind, h]

lemma Gdt.eval_bang_of_not_bottom { var: Var } { tr: Gdt } { env: Env }
    (h: is_bottom var env = ff):
    (Gdt.grd (Grd.bang var) tr).eval env = tr.eval env :=
by simp [Gdt.eval, Grd.eval, Result.bind, h]

@[simp]
lemma Gdt.eval_bang_no_match_iff { var: Var } { tr: Gdt } { env: Env }:
    (Gdt.grd (Grd.bang var) tr).eval env = Result.no_match ↔ is_bottom var env = ff ∧ tr.eval env = Result.no_match :=
by cases c: is_bottom var env; simp [Gdt.eval, Grd.eval, Result.bind, c]

lemma Gdt.eval_branch_replace_right_env { gdt₁ gdt₂ gdt₂': Gdt } { env: Env }
    (h: gdt₂.eval env = gdt₂'.eval env ∨ gdt₁.eval env ≠ Result.no_match):
    (gdt₁.branch gdt₂).eval env = (gdt₁.branch gdt₂').eval env :=
by by_cases x: gdt₁.eval env = Result.no_match; finish [Gdt.eval_branch_left, Gdt.eval_branch_right, x]


lemma Gdt.rhs_mem_rhss_of_eval_rhs { gdt: Gdt } { env: Env } { rhs: Rhs } (h: gdt.eval env = Result.value rhs): rhs ∈ gdt.rhss :=
begin
    induction gdt with rhs generalizing env,
    case Gdt.rhs {
        finish [Gdt.rhss, Gdt.eval],
    },
    case Gdt.grd {
        cases gdt_grd,
        case Grd.tgrd {
            cases c: tgrd_eval gdt_grd env,
            { finish [Gdt.rhss, Gdt.eval_tgrd_of_none c, Gdt.eval, Grd.eval, Result.bind], },
            { finish [Gdt.rhss, Gdt.eval_tgrd_of_some c, Gdt.eval, Grd.eval, Result.bind], },
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
