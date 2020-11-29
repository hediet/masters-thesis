import tactic
import .defs
import .lemmas

variable [GuardModule]
open GuardModule

lemma foo (ant: Ant Φ) (ty: Φ) (env: Env):
    ant_eval (map_ant (ty.and) ant) env
    = ant_eval' (map_ant (band (Φ_eval ty env)) (ant_eval_all ant env)) :=
begin
    sorry
end

-- for the sake of lean, it must be possible to simplify this drastically.
lemma and_no_match (ant: Ant Φ) (ty: Φ) (env: Env):
    ant_eval ant env = some Result.no_match
    → ant_eval (map_ant (ty.and) ant) env = some Result.no_match :=
begin
    assume h,
    rw ant_eval,
    rw ant_eval_all,
    
    induction ant,

    case Ant.leaf {
        rw ant_eval at h,
        rw ant_eval_all at h,
        rw map_ant at h,
        rw ant_eval' at h,
        cases c: Φ_eval ant_a env,
        all_goals {
            rw c at h,
            simp at h,
        },
        case bool.tt {
            cc,
        },
        rw map_ant,
        rw map_ant,
        rw ant_eval',
        rw Φ_eval,
        finish,
    },

    case Ant.branch {
        rw ant_eval at h,
        rw ant_eval_all at h,
        rw map_ant at h,
        rw ←ant_eval_all at h,
        rw ←ant_eval_all at h,
        rw ant_eval' at h,
        
        
        rw ←ant_eval at h,
        rw ←ant_eval at h,

        rw map_ant,
        rw map_ant,
        rw ant_eval',

        by_cases c1: (ant_eval ant_tr1 env = some Result.no_match),
        all_goals {
            by_cases c2: (ant_eval ant_tr2 env = some Result.no_match),
        },

        {
            cc,
        },
        {
            rw c1 at ant_ih_tr1,
            rw c1 at h,
            simp at ant_ih_tr1,
            rw ant_ih_tr1,
            
            cases ant_eval ant_tr2 env,
            case option.none {
                rw ant_eval'._match_1 at h,
                cc,
            },
            case option.some {
                cases val,
                all_goals {
                    rw ant_eval'._match_1 at h,
                    cc,
                },
            },
        },
        {
            rw c2 at ant_ih_tr2,
            rw c2 at h,
            simp at ant_ih_tr2,
            rw ant_ih_tr2,
            cases ant_eval ant_tr1 env,
            case option.none {
                rw ant_eval'._match_1 at h,
                cc,
            },
            case option.some {
                cases val,
                all_goals {
                    rw ant_eval'._match_1 at h,
                    cc,
                },
            },
        },
        {
            cases ant_eval ant_tr1 env,
            all_goals {
                cases ant_eval ant_tr2 env,
            },
            case option.none option.none {
                rw ant_eval'._match_1 at h,
                cc,
            },
            case option.some option.none {
                cases val,
                all_goals {
                    rw ant_eval'._match_1 at h,
                    cc,
                },
            },
            case option.none option.some {
                cases val,
                all_goals {
                    rw ant_eval'._match_1 at h,
                    cc,
                },
            },
            case option.some option.some {
                cases val,
                all_goals {
                    cases val_1,
                },
                all_goals {
                    rw ant_eval'._match_1 at h,
                    cc,
                },
            },
        },
    },
    case Ant.diverge {
        rw ant_eval at h,
        rw ant_eval_all at h,
        rw map_ant at h,
        rw ant_eval' at h,

        rw map_ant,
        rw map_ant,
        rw ant_eval',
        rw ←ant_eval_all at h,
        rw ←ant_eval at h,

        have x : ant_eval ant_tr env = some Result.no_match, {
            cases Φ_eval ant_a env,
            all_goals {
                cases ant_eval ant_tr env,
            },
            all_goals {
                try {
                    cases val,
                },
            },
            case bool.ff option.some Result.leaf {
                rw ant_eval'._match_2 at h,
                cc,
            },
            case bool.ff option.some Result.diverged {
                rw ant_eval'._match_2 at h,
                cc,
            },
            all_goals {
                finish,
            },
        },

        rw x at ant_ih,
        simp at ant_ih,
        rw ant_ih,
        cases c: Φ_eval (ty.and ant_a) env,
        all_goals {
            rw ant_eval'._match_2,
        },
        rw x at h,
        rw Φ_eval at c,
        have y: Φ_eval ant_a env = tt, {
            rw band_eq_true_eq_eq_tt_and_eq_tt at c,
            exact c.right,
        },
        rw y at h,
        rw ant_eval'._match_2 at h,
        cc,
    },
end

lemma ant_eval_is_some_and (ant: Ant Φ) (env: Env) (ty: Φ):
    option.is_some (ant_eval ant env)
    → option.is_some (ant_eval (map_ant (ty.and) ant) env) :=
begin
    assume h,
    induction ant with h2,
    
        
    
    case Ant.leaf {
        unfold 𝒜' map_ant ant_eval ant_eval ant_eval_all map_ant ant_eval',
        cases Φ_eval (ty.and h2) env,
        all_goals { simp },
    },

    case Ant.branch {
        
        conv at h {
            rw ant_eval,
            rw ant_eval_all,
            rw map_ant,
            rw ant_eval',
            rw ← ant_eval_all,
            rw ← ant_eval_all,
            rw ←ant_eval,
            rw ←ant_eval,
        },

        conv {
            rw map_ant,
            rw ant_eval,
            rw ant_eval_all,
            rw map_ant,
            rw ant_eval',
            rw ← ant_eval_all,
            rw ← ant_eval_all,
            rw ←ant_eval,
            rw ←ant_eval,
        },
        
        
        by_cases h_1: (ant_eval ant_tr1 env = some Result.no_match),
        all_goals {
            by_cases h_2: (ant_eval ant_tr2 env = some Result.no_match),
        },
        {
            rw h_1 at ant_ih_tr1,
            simp at ant_ih_tr1,
            rw h_2 at ant_ih_tr2,
            simp at ant_ih_tr2,
            rw and_no_match,
            rw and_no_match,
            rw ant_eval'._match_1,
            simp,
            exact h_2,
            exact h_1,
        },
        
        


        /-
        conv in (ant_eval (map_ant ty.and (𝒜' (gdt_tr1.branch gdt_tr2))) env).is_some {
            rw 𝒜',
            rw map_ant,
            rw ant_eval,
            rw ant_eval_all,
            rw map_ant,
            rw ant_eval',
            rw ← ant_eval_all,
            rw ← ant_eval_all,
            rw ←ant_eval,
            rw ←ant_eval,
        },
        -/
        
        
        /-
        rw map_ant at h,
        rw ← ant_eval_all at h,
        rw ← ant_eval_all at h,

        rw ant_eval' at h,
        rw ←ant_eval at h,
        rw ←ant_eval at h,
        
        rw map_ant at h,
        rw ant_eval' at h,
        -/
    },
end

-- 𝒜 maintains semantics
-- This theorem implies that ant_eval returns a list of length at most 1.
-- This means that the refinement types created by 𝒜 are disjoint.
theorem 𝒜_eval :
    ∀ env: Env, ∀ gdt: Gdt,
        some (gdt_eval gdt env) = ant_eval (𝒜 gdt) env :=
begin
    assume env,
    assume gdt,
    rw 𝒜_𝒜'_equiv,
    
    induction gdt with env,

    case Gdt.leaf {
        sorry,
        --finish,
    },

    case Gdt.branch {
        unfold 𝒜',
        unfold ant_eval,
        unfold ant_eval_all,
        unfold map_ant,
        rw ←ant_eval_all,
        rw ←ant_eval_all,
        unfold ant_eval',
        rw ←ant_eval,
        rw ←ant_eval,
        rw ←gdt_ih_tr1,


        cases c: (ant_eval (map_ant (𝒰' gdt_tr1).and (𝒜' gdt_tr2)) env),

        case option.none {

        },





        cases (gdt_eval gdt_tr1 env),
        all_goals {
            cases (ant_eval (map_ant (𝒰' gdt_tr1).and (𝒜' gdt_tr2)) env),
        },
        all_goals {
            try {
                cases val,
            },
        },

        all_goals {
            unfold ant_eval'._match_1,
        },
        repeat {
            simp,
        },

        
        
        unfold gdt_eval,

    },

end