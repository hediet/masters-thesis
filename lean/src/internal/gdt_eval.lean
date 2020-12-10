import tactic
import ..definitions
import .helper_defs

variable [GuardModule]
open GuardModule

@[simp]
lemma gdt_eval_branch_left_no_match { gdt1: Gdt } { gdt2: Gdt } { env: Env } (h: gdt1.eval env = Result.no_match):
            (Gdt.branch gdt1 gdt2).eval env = gdt2.eval env :=
begin
    cases c: gdt2.eval env;
    finish [Gdt.eval],
end

@[simp]
lemma gdt_eval_branch_right_no_match { gdt1: Gdt } { gdt2: Gdt } { env: Env } (h: gdt2.eval env = Result.no_match):
            (Gdt.branch gdt1 gdt2).eval env = gdt1.eval env :=
begin
    cases c: gdt1.eval env;
    finish [Gdt.eval],
end

@[simp]
lemma gdt_eval_branch_no_match { gdt1: Gdt } { gdt2: Gdt } { env: Env }:
    (Gdt.branch gdt1 gdt2).eval env = Result.no_match ↔ gdt1.eval env = Result.no_match ∧ gdt2.eval env = Result.no_match :=
begin
    cases c1: gdt1.eval env;
    cases c2: gdt2.eval env;
    finish [Gdt.eval, Gdt.eval._match_2,  Gdt.eval._match_1],
end

@[simp]
lemma gdt_leaf_eval { leaf: Leaf } { env: Env }: (Gdt.leaf leaf).eval env = Result.leaf leaf :=
by simp [Gdt.eval]

lemma grd_eval_xgrd_some { grd: XGrd } { tr: Gdt } { env env': Env }
    (h: xgrd_eval grd env = some env'):
    (Gdt.grd (Grd.xgrd grd) tr).eval env = tr.eval env' :=
by simp [Gdt.eval, h]

lemma grd_eval_xgrd_none { grd: XGrd } { tr: Gdt } { env: Env }
    (h: xgrd_eval grd env = none):
    (Gdt.grd (Grd.xgrd grd) tr).eval env = Result.no_match :=
by simp [Gdt.eval, h]

lemma grd_eval_bang_bottom { var: Var } { tr: Gdt } { env: Env }
    (h: is_bottom var env = tt):
    (Gdt.grd (Grd.bang var) tr).eval env = Result.diverged :=
by simp [Gdt.eval, h]

lemma grd_eval_bang_not_bottom { var: Var } { tr: Gdt } { env: Env }
    (h: is_bottom var env = ff):
    (Gdt.grd (Grd.bang var) tr).eval env = tr.eval env :=
by simp [Gdt.eval, h]

