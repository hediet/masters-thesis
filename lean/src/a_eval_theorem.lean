import tactic
import .defs
import .lemmas

variable [GuardModule]
open GuardModule

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

attribute [simp]
lemma ant_eval'_simp4 (r: option Result) :
    ant_eval'._match_2 (ff, r) = r :=
begin
    cases r;
    try { cases r };
    finish,
end

attribute [simp]
lemma ant_eval'_simp5 (r: option Result) (h: r ≠ some Result.no_match) :
    ant_eval'._match_2 (tt, r) = none :=
begin
    cases r;
    try { cases r };
    finish,
end


local attribute [simp] 𝒜' ant_eval ant_eval_all map_ant ant_eval' Φ_eval gdt_eval 

lemma and_no_match (ant: Ant Φ) (ty: Φ) (env: Env) (h: ant_eval ant env = some Result.no_match):
    ant_eval (map_ant (ty.and) ant) env = some Result.no_match :=
begin
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
        simp at h, rw [←ant_eval_all, ←ant_eval] at h,
        simp, rw [←ant_eval_all, ←ant_eval],

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



lemma ant_eval_is_some_and (ant: Ant Φ) (env: Env) (ty: Φ) (h: option.is_some (ant_eval ant env)):
    option.is_some (ant_eval (map_ant (ty.and) ant) env) :=
begin
    induction ant with h2,
    

    case Ant.leaf {
        simp,
        by_cases ↥(Φ_eval ty env) ∧ ↥(Φ_eval h2 env);
        finish,
    },

    case Ant.branch {
        
        conv at h {
            simp,
            rw ← ant_eval_all,
            rw ← ant_eval_all,
            rw ←ant_eval,
            rw ←ant_eval,
        },

        conv {
            simp,
            rw ← ant_eval_all,
            rw ←ant_eval,
            rw ← ant_eval_all,
            rw ←ant_eval,
        },
        
        by_cases h_1: (ant_eval ant_tr1 env = some Result.no_match);
        by_cases h_2: (ant_eval ant_tr2 env = some Result.no_match),
        
        {
            rw (and_no_match _ _ _ h_1),
            rw (and_no_match _ _ _ h_2),
            simp,
        },
        {
            rw (and_no_match _ _ _ h_1),
            rw ant_eval'_simp1,
            rw h_1 at h,
            rw ant_eval'_simp1 at h,
            exact ant_ih_tr2 h,
        },
        {
            rw (and_no_match _ _ _ h_2),
            rw ant_eval'_simp2,
            rw h_2 at h,
            rw ant_eval'_simp2 at h,
            exact ant_ih_tr1 h,
        },
        {
            rw ant_eval'_simp3 at h,
            simp at h,
            contradiction,
            exact h_1,
            exact h_2,
        },
    },

    case Ant.diverge {
        simp,
        rw ← ant_eval_all,
        rw ←ant_eval,

        simp at h,
        rw ← ant_eval_all at h,
        rw ←ant_eval at h,


        cases Φ_eval ant_a env;
        by_cases x: ant_eval ant_tr env = some Result.no_match,
        all_goals {
            simp,
            rw ← ant_eval_all,
            rw ←ant_eval,
        },

        {
            rw and_no_match _ _ _ x,
            simp,
        },
        {
            simp at h,
            rw ← ant_eval_all at h,
            rw ←ant_eval at h,
            exact ant_ih h,
        },
        {
            rw and_no_match _ _ _ x,
            cases Φ_eval ty env;
            simp,
        },
        {
            rw ant_eval'_simp5 at h,
            simp at h,
            contradiction,
            exact x,
        },
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
        simp,
        rw [←ant_eval_all, ←ant_eval],
        rw [←ant_eval_all, ←ant_eval],
        


/-
    gdt_ih_tr1: some (gdt_eval gdt_tr1 env) = ant_eval (𝒜' gdt_tr1) env
    gdt_ih_tr2: some (gdt_eval gdt_tr2 env) = ant_eval (𝒜' gdt_tr2) env

        some (
            gdt_eval._match_1
                (gdt_eval gdt_tr2 env)
                (gdt_eval gdt_tr1 env)
        )
        
        = ant_eval'._match_1
            (
                ant_eval (𝒜' gdt_tr1) env,
                ant_eval (map_ant (𝒰' gdt_tr1).and (𝒜' gdt_tr2)) env
            )















    gdt_ih_tr1: some (gdt_eval gdt_tr1 env) = ant_eval (𝒜' gdt_tr1) env
    gdt_ih_tr2: some (gdt_eval gdt_tr2 env) = ant_eval (𝒜' gdt_tr2) env

        some (
            match gdt_eval gdt_tr1 env with
            | Result.no_match := gdt_eval gdt_tr2 env
            | r := r
            end
        )
        =
            match (ant_eval (𝒜' gdt_tr1) env, ant_eval (map_ant (𝒰' gdt_tr1).and (𝒜' gdt_tr2)) env) with
            | (some Result.no_match, r) := r
            | (r, some Result.no_match) := r
            | _ := none
            end

















    gdt_ih_tr1: some (gdt_eval gdt_tr1 env) = ant_eval (𝒜' gdt_tr1) env
    gdt_ih_tr2: some (gdt_eval gdt_tr2 env) = ant_eval (𝒜' gdt_tr2) env

        some (
            match gdt_eval gdt_tr1 env with
                | Result.no_match := gdt_eval gdt_tr2 env
                | r := r
            end
        )
        =
            match (
                some (gdt_eval gdt_tr1 env),
                ant_eval (map_ant (𝒰' gdt_tr1).and (𝒜' gdt_tr2)) env
            ) with
                | (some Result.no_match, r) := r
                | (r, some Result.no_match) := r
                | _ := none
            end




-/


        cases c: (ant_eval (map_ant (𝒰' gdt_tr1).and (𝒜' gdt_tr2)) env),

        case option.none {
            have x: (option.is_some (ant_eval (𝒜' gdt_tr2) env) : Prop) := begin
                rw ←gdt_ih_tr2,
                simp,
            end,
            let q := (ant_eval_is_some_and _ _ _ x), 
            rw c at q,
            simp at q,
            contradiction,
        },



        rw ←gdt_ih_tr1,











        

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