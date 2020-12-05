import tactic
import .defs
import .lemmas
import .u_eval_theorem

variable [GuardModule]
open GuardModule
variable [decidable_eq Leaf]

/-
Does this help?

lemma ant_eval'_simp6 (tr: Ant Φ) (env: Env) :
    ant_eval' (map_ant (λ (ty : Φ), Φ_eval ty env) tr)
    = ant_eval tr env :=
begin
    simp [ant_eval, ant_eval_all, map_ant ant_eval', gdt_eval],
end
-/


@[simp] lemma ant_eval'_simp1 (r: option Result) :
    ant_eval'._match_1 (some Result.no_match) r = r :=
begin
    cases r,
    finish,
    cases r;
    finish,
end

@[simp] lemma ant_eval'_simp2 (r: option Result) :
    ant_eval'._match_1 r (some Result.no_match) = r :=
begin
    cases r,
    finish,
    cases r;
    finish,
end

@[simp] lemma ant_eval'_simp3 (r1: option Result) (r2: option Result) :
    r1 ≠ some Result.no_match
    → r2 ≠ some Result.no_match
    → ant_eval'._match_1 r1 r2 = none :=
begin
    cases r1;
    try { cases r1 };
    cases r2;
    try { cases r2 };
    finish,    
end

@[simp] lemma ant_eval'_simp4 (r: option Result) :
    ant_eval'._match_2 ff r = r :=
begin
    cases r;
    try { cases r };
    finish,
end

@[simp] lemma ant_eval'_simp5 (r: option Result) (h: r ≠ some Result.no_match) :
    ant_eval'._match_2 tt r = none :=
begin
    cases r;
    try { cases r };
    finish,
end


local attribute [simp] 𝒜' ant_eval ant_eval_all map_ant ant_eval' Φ_eval gdt_eval is_no_match

lemma and_no_match { ant: Ant Φ } { ty: Φ } { env: Env } (h: ant_eval ant env = some Result.no_match):
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
        -- h: ant_eval (Ant.diverge ant_a ant_tr) env = some Result.no_match
        simp at h,
        -- h: ant_eval'._match_2 (Φ_eval ant_a env) (ant_eval' (map_ant (λ (ty : Φ), Φ_eval ty env) ant_tr)) = some Result.no_match
        rw [←ant_eval_all, ←ant_eval] at h,
        -- h: ant_eval'._match_2 (Φ_eval ant_a env) (ant_eval ant_tr env) = some Result.no_match

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

/-
Does this help?

lemma foo (ty: Φ) (d: Φ) (tr: Ant Φ) (tr2: Ant Φ) (env: Env) :
    ant_eval (map_ant ty.and (Ant.diverge d tr)) env
    = ant_eval'._match_2 (Φ_eval ty env && Φ_eval d env, ant_eval (map_ant ty.and tr) env) :=
begin
    simp [ant_eval, ant_eval_all, map_ant ant_eval', gdt_eval],
end
-/

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
            /-
             (h: ant_eval ant env = some Result.no_match)
                → (ant_eval (map_ant (ty.and) ant) env = some Result.no_match)
            -/

            simp [and_no_match, *],
        },
        {
            rw (and_no_match h_1),
            rw ant_eval'_simp1,
            rw h_1 at h,
            rw ant_eval'_simp1 at h,
            exact ant_ih_tr2 h,
        },
        {
            rw (and_no_match h_2),
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
            rw and_no_match x,
            simp,
        },
        {
            simp at h,
            rw ← ant_eval_all at h,
            rw ←ant_eval at h,
            exact ant_ih h,
        },
        {
            rw and_no_match x,
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

lemma map_ant_associative { α: Type _ } { β: Type _ } { γ: Type _ } (f: β → γ) (g: α → β) (ant: Ant α):
    map_ant f (map_ant g ant) = map_ant (f ∘ g) ant :=
begin
    induction ant;
    finish,
end


@[simp] lemma ant_eval_all_false (ant: Ant Φ) : ant_eval' (map_ant (λ (x : Φ), ff) ant) = some Result.no_match :=
begin
    induction ant;
    finish,
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
    
    induction gdt generalizing env,

    case Gdt.leaf {
        finish,
    },

    case Gdt.branch {
/-
    Goal:

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
                ant_eval (𝒜' gdt_tr1) env,
                ant_eval (map_ant (𝒰' gdt_tr1).and (𝒜' gdt_tr2)) env
            ) with
                | (some Result.no_match, r) := r
                | (r, some Result.no_match) := r
                | _ := none
            end
-/

        simp,
        rw [←ant_eval_all, ←ant_eval],
        rw [←ant_eval_all, ←ant_eval],

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

        cases c2: (gdt_eval gdt_tr1 env),

        case Result.leaf {
            simp,
            rw ant_eval at c,
            rw ant_eval_all at c,
            rw map_ant_associative at c,
            rw function.comp at c,
            
            simp at c,
            rw ←𝒰_𝒰'_equiv at c,
            rw 𝒰_eval at c,
            rw c2 at c,
            simp at c,
            rw ←c,
            simp,
        },

        case Result.diverged {
            simp,
            rw ant_eval at c,
            rw ant_eval_all at c,
            rw map_ant_associative at c,
            rw function.comp at c,
            
            simp at c,
            rw ←𝒰_𝒰'_equiv at c,
            rw 𝒰_eval at c,
            rw c2 at c,
            simp at c,
            rw ←c,
            simp,
        },

        case Result.no_match {
            simp,
            rw ant_eval at c,
            rw ant_eval_all at c,
            rw map_ant_associative at c,
            rw function.comp at c,

            simp at c,
            rw ←𝒰_𝒰'_equiv at c,
            rw 𝒰_eval at c,
            rw c2 at c,
            simp at c,
            rw [←ant_eval_all, ←ant_eval] at c,
            rw ← gdt_ih_tr2 at c,
            simp at c,
            rw c,
        },
    },

    case Gdt.grd {
        cases c: gdt_grd;
        simp,
        case Grd.xgrd {
            rw map_ant_associative,
            rw function.comp,
            simp,
            cases x: xgrd_eval xgrd env;
            simp,
            rw [←ant_eval_all, ←ant_eval],
            rw gdt_ih,
        },

        case Grd.bang {
            rw map_ant_associative,
            rw function.comp,
            simp,

            cases x: is_bottom var env;
            simp,
            rw [←ant_eval_all, ←ant_eval],
            rw gdt_ih,
        }
    },
end

lemma foo_bar { α: Type } { β: Type } { ant: Ant α } { ls: list Leaf } { f: α → β }
        (h: map_ant_option f (ant_remove_leaves ls ant) = none):
        ant_remove_leaves ls ant = none :=
begin
    cases ant_remove_leaves ls ant,
    simp,
    rw map_ant_option at h,
    simp at h,
    contradiction,
end

/-



-/

/-
def 𝒜'_option: option Gdt -> option (Ant Φ)
| (some gdt) := some (𝒜' gdt)
| none := none

lemma ant_removes_leaves_map_ant_homomorph { α: Type } { β: Type } (ant: Ant α) (ls: list Leaf) (f: α → β) :
        ant_remove_leaves ls (map_ant f ant) = map_ant_option f (ant_remove_leaves ls ant) :=
begin
    induction ant,
    case Ant.leaf {
        by_cases ant_leaf ∈ ls;
        simp [h, map_ant_option, ant_remove_leaves, map_ant],
    },
    case Ant.branch {
        rw [map_ant, ant_remove_leaves, ant_ih_tr1, ant_ih_tr2, ant_remove_leaves],
        cases ant_remove_leaves ls ant_tr1;
        cases ant_remove_leaves ls ant_tr2;
        simp [map_ant_option, ant_remove_leaves, ant_remove_leaves._match_1],
    },
    case Ant.diverge {
        rw [map_ant, ant_remove_leaves, ant_ih, ant_remove_leaves],
        cases ant_remove_leaves ls ant_tr;
        simp [map_ant_option, ant_remove_leaves, ant_remove_leaves._match_1, map_ant],
    },
end

lemma remove_leaves_none (gdt: Gdt) (ls: list Leaf):
    (gdt_remove_leaves ls gdt = none) ↔ (ant_remove_leaves ls (𝒜' gdt) = none) :=
begin
    induction gdt with leaf,

    case Gdt.leaf {
        rw [gdt_remove_leaves, 𝒜', ant_remove_leaves],
        by_cases leaf ∈ ls;
        simp [h],
    },

    case Gdt.grd {
        cases gdt_grd,
        {
            rw 𝒜',
            rw ant_removes_leaves_map_ant_homomorph,
            rw gdt_remove_leaves,
            cases gdt_remove_leaves ls gdt_tr;
            cases ant_remove_leaves ls (𝒜' gdt_tr);
            finish [ant_remove_leaves, map_ant_option, gdt_remove_leaves._match_2],
        },
        {
            rw 𝒜',
            rw ant_remove_leaves,
            rw ant_removes_leaves_map_ant_homomorph,
            rw gdt_remove_leaves,
            cases gdt_remove_leaves ls gdt_tr;
            cases ant_remove_leaves ls (𝒜' gdt_tr);
            finish [ant_remove_leaves, map_ant_option, gdt_remove_leaves._match_2],
        },
    },

    case Gdt.branch {
        rw [gdt_remove_leaves, 𝒜', ant_remove_leaves],
        rw ant_removes_leaves_map_ant_homomorph,
        cases gdt_remove_leaves ls gdt_tr1;
        cases gdt_remove_leaves ls gdt_tr2;
        cases ant_remove_leaves ls (𝒜' gdt_tr1);
        cases ant_remove_leaves ls (𝒜' gdt_tr2);
        finish [gdt_remove_leaves._match_1, gdt_ih_tr1, gdt_ih_tr2],
    },
end

lemma xyz (gdt: Gdt) (ls: list Leaf):
    ant_eval_option (ant_remove_leaves ls (𝒜' gdt)) = ant_eval_option (𝒜'_option (gdt_remove_leaves ls gdt)) :=
begin
    ext env:1,
    induction gdt with leaf,

    case Gdt.leaf {
        by_cases x: leaf ∈ ls;
        --finish [ant_remove_leaves, gdt_remove_leaves, 𝒜', 𝒜'_option],
        sorry,
    },

    case Gdt.branch {
        simp [ant_remove_leaves, gdt_remove_leaves, 𝒜', 𝒜'_option],

        cases c1: gdt_remove_leaves ls gdt_tr1;
        cases c2: gdt_remove_leaves ls gdt_tr2,

        simp [ant_eval_option, ant_eval_option, ant_remove_leaves, ant_remove_leaves._match_1, gdt_eval_option, gdt_remove_leaves, 𝒜'],
        {
            /-
            have h1 : ant_remove_leaves ls (𝒜' gdt_tr1) = none :=
            begin
                finish [remove_leaves_none],
            end,
            have h2 : ant_remove_leaves ls (map_ant (𝒰' gdt_tr1).and (𝒜' gdt_tr2)) = none :=
            begin
                finish [ant_removes_leaves_map_ant_homomorph, remove_leaves_none],
            end,

            finish,
            -/
            sorry,
        },
        {
            have h1 : ant_remove_leaves ls (𝒜' gdt_tr1) = none :=
            begin
                --finish [remove_leaves_none],
                sorry,
            end,

            rw h1,
            rw gdt_remove_leaves._match_1,
            rw 𝒜'_option,
            rw ant_eval_option,

            have h2 : ∃ v2: Ant Φ, ant_remove_leaves ls (map_ant (𝒰' gdt_tr1).and (𝒜' gdt_tr2)) = some v2 :=
            begin
                cases c3: ant_remove_leaves ls (map_ant (𝒰' gdt_tr1).and (𝒜' gdt_tr2)),
                {
                    rw ant_removes_leaves_map_ant_homomorph at c3,
                    replace c3 := foo_bar c3,
                    rw ←remove_leaves_none at c3,
                    rw c2 at c3,
                    simp at c3,
                    contradiction,
                },
                simp,
            end,

            cases h2,
            rw h2_h,
            rw ant_remove_leaves._match_1,
            rw ant_eval_option,
            rw ant_removes_leaves_map_ant_homomorph at h2_h,
            rw c2 at gdt_ih_tr2,
            rw 𝒜'_option at gdt_ih_tr2,
            rw ant_eval_option at gdt_ih_tr2,
            rw ←gdt_ih_tr2,
        }
    }
end
-/


/-
lemma xyz1 (gdt: Gdt) (ls: list Leaf) (env: Env):
    ant_eval_option (ant_remove_leaves ls (𝒜' gdt)) env = some (gdt_eval_option (gdt_remove_leaves ls gdt) env) :=
begin
    induction gdt with leaf,

    case Gdt.leaf {
        by_cases x: leaf ∈ ls;
        finish [ant_eval_option, ant_remove_leaves, gdt_eval_option, gdt_remove_leaves, 𝒜'],
    },

    case Gdt.branch {
        simp [ant_eval_option, ant_remove_leaves, gdt_eval_option, gdt_remove_leaves, 𝒜'],

        cases ant_remove_leaves ls (𝒜' gdt_tr1);
        cases ant_remove_leaves ls (map_ant (𝒰' gdt_tr1).and (𝒜' gdt_tr2)),
        simp [ant_eval_option, ant_remove_leaves, ant_remove_leaves._match_1, gdt_eval_option, gdt_remove_leaves, 𝒜'],
    }
end
-/