import tactic
import .a_eval_theorem

import .defs
variable [GuardModule]
open GuardModule

local attribute [simp] ant_eval'._match_2

lemma foo (tr1: Ant Φ) (tr2: Ant Φ) (env: Env):
    ant_eval (tr1.branch tr2) env
    = ant_eval'._match_1 (ant_eval tr1 env) (ant_eval tr2 env) :=
begin
    simp [ant_eval, ant_eval_all, map_ant, ant_eval'],
end

lemma foo_1 (tr: Ant Φ) (ty: Φ) (env: Env):
    ant_eval (Ant.diverge ty tr) env
    = ant_eval'._match_2 (Φ_eval ty env) (ant_eval tr env) :=
begin
    simp [ant_eval, ant_eval_all, map_ant, ant_eval'],
end

lemma ant_eval_branch (tr1: Ant Φ) (tr2: Ant Φ) (env: Env) (r: Result)
    (h: ant_eval (tr1.branch tr2) env = some r):
        ant_eval tr1 env = some r ∨ ant_eval tr2 env = some r :=
begin
    rw foo at h,
    cases ant_eval tr1 env with val1;
    try { cases val1, };
    cases ant_eval tr2 env with val2;
    try { cases val2, };
    finish
end

lemma ant_eval_diverge { ty: Φ } { tr: Ant Φ } { env: Env } { r: Result }
    (h: ant_eval (Ant.diverge ty tr) env = some r):
        Φ_eval ty env == ff ∧ ant_eval tr env = some r
        ∨ Φ_eval ty env == tt ∧ r = Result.diverged :=
begin
    rw foo_1 at h,
    cases Φ_eval ty env;
    cases ant_eval tr env with val;
    try { cases val, };
    finish,
end

def ℛ'_diverge (a: list Leaf) (i: list Leaf) (r: list Leaf) (is_empty: bool) (ant: Ant bool)
    (h1: ℛ' ant = (a, i, r)):
    (is_empty = false ∧ a = [] ∧ i = []  ∧ ∃ rh: Leaf, ∃ rs: list Leaf, r = rh::rs ∧ ℛ' (Ant.diverge is_empty ant) = ([], [rh], rs))
    ∨ ((is_empty = true ∨ a ≠ [] ∨ i ≠ [] ∨ r = []) ∧ ℛ' (Ant.diverge is_empty ant) = (a, i, r)) :=
begin
    cases is_empty;
    cases a;
    cases i;
    cases r;
    simp [ℛ', ℛ'._match_1, h1],
end

-- (a, i, r) = ℛ is_empty.val (Ant.diverge ant_a ant_tr)

def ℛ'_diverge' (ty: Φ) (tr: Ant Φ) (): sorry := sorry

lemma r_correct_1 [decidable_eq Leaf]
    (is_empty: Gs) (gdt: Gdt)
    
    (ant: Ant Φ)
    (h1: ant_eval ant = some ∘ gdt_eval gdt)

    (a: list Leaf) (i: list Leaf) (r: list Leaf)
    (h2: (a, i, r) = ℛ is_empty.val ant)
    
    (env: Env) (leaf: Leaf)
    (h3: gdt_eval gdt env = Result.leaf leaf):

        leaf ∈ a

    :=
begin
    replace h3: ant_eval ant env = some(Result.leaf leaf), sorry, -- finish
    clear h1,
    
    induction ant generalizing a i r env,

    case Ant.branch {
        sorry,
        /-
        rw ℛ at h2,
        rw map_ant at h2,
        rw ℛ' at h2,
        rw ←ℛ at h2,
        rw ←ℛ at h2,

        replace h3 := ant_eval_branch h3,

        cases ℛ is_empty.val ant_tr1 with tr1_a tr1_,
        cases tr1_ with tr1_i tr1_r,

        cases ℛ is_empty.val ant_tr2 with tr2_a tr2_,
        cases tr2_ with tr2_i tr2_r,


        rw ℛ'._match_2 at h2,

        cases h3,

        case or.inl {
            have: leaf ∈ tr1_a := begin
                specialize ant_ih_tr1 tr1_a tr1_i tr1_r env,
                simp at ant_ih_tr1,
                rw h3 at ant_ih_tr1,
                simp at ant_ih_tr1,
                exact ant_ih_tr1,
            end,
            finish,
        },

        case or.inr {
            have: leaf ∈ tr2_a := begin
                specialize ant_ih_tr2 tr2_a tr2_i tr2_r env,
                simp at ant_ih_tr2,
                rw h3 at ant_ih_tr2,
                simp at ant_ih_tr2,
                exact ant_ih_tr2,
            end,
            finish,
        },
        -/
    },

    case Ant.diverge {
        rw ℛ at h2,
        rw map_ant at h2,
        rw ℛ' at h2,
        rw ←ℛ at h2,

        replace h3 := ant_eval_diverge h3,
        cases ℛ is_empty.val ant_tr with tr_a tr_,
        cases tr_ with tr_i tr_r,

        have x := ℛ'_diverge a i r (is_empty.val ant_a) (map_ant is_empty.val ant_tr),
        rw ℛ at h2,
        rw h2 at x,

        rw ℛ'._match_1 at h2,
    },
end


#print prefix ℛ'._match_1

























-- Every redundant leaf can be marked as inaccessible instead and
-- every inaccessible leaf can be marked as accessible instead without invalidating the theorem. This only weakens the analysis.

theorem r_correct [decidable_eq Leaf] : ∀ gdt: Gdt, ∀ is_empty: Gs,
    (
        -- structure + später matchen
        let ⟨ a, i, r ⟩ := ℛ is_empty.val $ 𝒜 gdt
        in
                -- Leaves that are redundant and neither accessible nor inaccessible can be removed without changing semantics.
                -- If all leaves are unique, a, i and r are disjoint.
                -- In that case, `r.remove_all (i ++ a)` = `r`.
                -- If all leaves are equal, `r.remove_all (i ++ a)` usually is the empty list.
                gdt_eval_option (remove_leaves (r.remove_all (i ++ a)) gdt)
                = gdt_eval gdt
            ∧ 
                -- reachable leaves are accessible.
                -- Since R is clearly a partition for disjoint leaves,
                -- this also means that non-accessible leaves are unreachable.
                ∀ env: Env,
                    (match gdt_eval gdt env with
                    | (Result.leaf leaf) := leaf ∈ a
                    | _ := true
                    end : Prop)
        : Prop
    )
    -- We probably need 𝒜_eval for proving this.
    :=
begin
    
end
