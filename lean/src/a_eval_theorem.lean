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

attribute [simp]
lemma ant_eval'_simp1 (r: option Result) :
    ant_eval'._match_1 (some Result.no_match, r) = r :=
begin
    cases r,
    finish,
    cases r;
    finish,
end

attribute [simp]
lemma ant_eval'_simp2 (r: option Result) :
    ant_eval'._match_1 (r, some Result.no_match) = r :=
begin
    cases r,
    finish,
    cases r;
    finish,
end

attribute [simp]
lemma ant_eval'_simp3 (r1: option Result) (r2: option Result) :
    r1 ≠ some Result.no_match
    → r2 ≠ some Result.no_match
    → ant_eval'._match_1 (r1, r2) = none :=
begin
    cases r1;
    try { cases r1 };
    cases r2;
    try { cases r2 };
    finish,    
end


local attribute [simp] ant_eval ant_eval_all map_ant ant_eval' Φ_eval

lemma and_no_match (ant: Ant Φ) (ty: Φ) (env: Env):
    ant_eval ant env = some Result.no_match
    → ant_eval (map_ant (ty.and) ant) env = some Result.no_match :=
begin
    assume h,
    
    induction ant,

    case Ant.leaf {
        have: Φ_eval ant_a env = ff, begin
            simp at h,
            cases Φ_eval ant_a env;
            finish,
        end,
        finish,
    },

    case Ant.branch {
        by_cases c1: (ant_eval ant_tr1 env = some Result.no_match);
        by_cases c2: (ant_eval ant_tr2 env = some Result.no_match);
        finish,
    },

    case Ant.diverge {
        simp at h,
        simp,

        rw ←ant_eval_all,
        rw ←ant_eval,
        rw ←ant_eval_all at h,
        rw ←ant_eval at h,

        have z : Φ_eval ant_a env = ff ∧ ant_eval ant_tr env = some Result.no_match, {
            cases Φ_eval ant_a env;
            cases ant_eval ant_tr env;
            try { cases val, };
            simp at h;
            cc,
        },
        
        finish,
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