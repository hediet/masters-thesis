import tactic

open tactic expr

namespace tactic
namespace interactive
setup_tactic_parser

private meta def try_specialize_all (v: pexpr) : tactic unit :=
do
    ctx ← local_context,
    ctx.mall (λ e,
        do
            try `[ specialize %%e %%v ],
            return tt
    ),
    skip

meta def induction_ant_disjoint (hp : parse cases_arg_p) (h : parse (tk "from" *> ident)) (rec_name : parse using_ident) (ids : parse with_ident_list)
  (revert : parse $ (tk "generalizing" *> ident*)?) : tactic unit :=
do
    induction hp rec_name ids revert,
    propagate_tags `[
        clear ant_disjoint
    ],
    rotate_right 1,
    propagate_tags `[
        unfold Ant.disjoint_rhss at ant_disjoint,
        try_specialize_all ```(ant_disjoint)
        --clear ant_disjoint
    ],
    rotate_right 1,
    propagate_tags `[
        unfold Ant.disjoint_rhss at ant_disjoint,
        try_specialize_all ```(ant_disjoint.1),
        try_specialize_all ```(ant_disjoint.2.1),
        replace ant_disjoint := ant_disjoint.2.2
    ],
    rotate_right 1,
    skip

meta def inline (h : parse parser.pexpr): tactic unit :=
do
    m ← match_local_const h,
    rewrite
        { rules:= [{pos := {line := 43, column := 11}, symm := ff, rule := h}], end_pos:=none }
        loc.wildcard,
    tactic.clear_lst [m.fst]

    

meta def R_diverge_cases: tactic unit :=
`[
    have R_diverge_cases := R_diverge_cases ant_tr ant_a,
    cases R_diverge_cases,

    cases R_diverge_cases with r R_diverge_cases,
    cases R_diverge_cases with rs R_diverge_cases,
    rw R_diverge_cases.2.2 at *,
    have R_ant_tr := R_diverge_cases.2.1,
    have ant_a := R_diverge_cases.1,
    clear R_diverge_cases,

    rotate 1,

    rw R_diverge_cases.2 at *,
    replace R_diverge_cases := R_diverge_cases.1,
    
    rotate 1
]

end interactive
end tactic
