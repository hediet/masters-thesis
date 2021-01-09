import tactic
import ...definitions
import ..internal_definitions
import .eval

variable [GuardModule]
open GuardModule

lemma Gdt.branch_option_replace_left_env { gdt₁ gdt₁' gdt₂: option Gdt } { env: Env }
    (h: Gdt.eval_option gdt₁ env = Gdt.eval_option gdt₁' env):
    Gdt.eval_option (Gdt.branch_option gdt₁ gdt₂) env = Gdt.eval_option (Gdt.branch_option gdt₁' gdt₂) env :=
by cases gdt₁; cases gdt₁'; cases gdt₂; finish [Gdt.branch_option, Gdt.eval_option, Gdt.eval, Gdt.eval_branch_right]

@[simp]
lemma Gdt.branch_option_first_none { gdt: option Gdt }: (Gdt.branch_option none gdt) = gdt :=
by cases gdt; simp [Gdt.branch_option]

lemma Gdt.branch_option_replace_right_env { gdt₁ gdt₂: option Gdt } (gdt₂': option Gdt) { env: Env }
    (h: Gdt.eval_option gdt₂ env = Gdt.eval_option gdt₂' env ∨ Gdt.eval_option gdt₁ env ≠ Result.no_match):
    Gdt.eval_option (Gdt.branch_option gdt₁ gdt₂) env = Gdt.eval_option (Gdt.branch_option gdt₁ gdt₂') env :=
begin
    cases gdt₁, { finish [Gdt.branch_option, Gdt.eval_option], },
    cases gdt₂, { cases gdt₂'; finish [Gdt.branch_option, Gdt.eval_option, Gdt.eval_branch_left], },
    cases gdt₂', { finish [Gdt.branch_option, Gdt.eval_option, Gdt.eval_branch_left], },
    simp only [Gdt.branch_option, Gdt.eval_option, Gdt.eval_branch_left] at *,
    exact Gdt.eval_branch_replace_right_env h,
end

@[simp]
lemma Gdt.eval_option_branch_option_some (gdt₁ gdt₂: Gdt) (env: Env):
  Gdt.eval_option (Gdt.branch_option (some gdt₁) (some gdt₂)) env = (gdt₁.branch gdt₂).eval env :=
by simp [Gdt.branch_option, Gdt.eval_option]

lemma Gdt.eval_option_of_xgrd_eval_some { grd: XGrd } { tr: option Gdt } { env env': Env }
    (h: xgrd_eval grd env = some env'):
    Gdt.eval_option (Gdt.grd_option (Grd.xgrd grd) tr) env = Gdt.eval_option tr env' :=
by cases tr; simp [Gdt.eval_option, Gdt.grd_option, Gdt.eval_xgrd_of_some h, *]

lemma Gdt.eval_option_of_xgrd_eval_none { grd: XGrd } { tr: option Gdt } { env: Env }
    (h: xgrd_eval grd env = none):
    Gdt.eval_option (Gdt.grd_option (Grd.xgrd grd) tr) env = Result.no_match :=
by cases tr; simp [Gdt.eval_option, Gdt.grd_option, Gdt.eval_xgrd_of_none h, *]

lemma Gdt.eval_option_of_is_bottom_ff { var: Var } { tr: option Gdt } { env: Env }
  (h: is_bottom var env = ff):
    Gdt.eval_option (Gdt.grd_option (Grd.bang var) tr) env = Gdt.eval_option tr env :=
by cases tr; simp [Gdt.grd_option, Gdt.eval_option, Gdt.eval_bang_of_not_bottom h]

lemma Gdt.eval_option_of_is_bottom_tt { var: Var } { tr: option Gdt } { env: Env }
  (h: is_bottom var env = tt) (g: tr ≠ none):
    Gdt.eval_option (Gdt.grd_option (Grd.bang var) tr) env = Result.diverged :=
by cases tr; finish [Gdt.grd_option, Gdt.eval_option, Gdt.eval, h]
