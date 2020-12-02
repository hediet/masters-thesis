import tactic
import .a_eval_theorem
import .defs
import .helper_defs

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

lemma ant_eval_branch { tr1: Ant Φ } { tr2: Ant Φ } { env: Env } { r: Result }
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

def R_diverge { is_empty: Φ → bool } { tr: Ant Φ } { r: LeafPartition } (ty: Φ)
    (h: R is_empty tr = r):
    (∃ rh: Leaf, ∃ rs: list Leaf, is_empty ty = ff ∧ r = ⟨ [], [], rh::rs ⟩ ∧ R is_empty (Ant.diverge ty tr) = ⟨ [], [rh], rs ⟩)
    ∨ ((is_empty ty = tt ∨ r.acc ≠ [] ∨ r.inacc ≠ [] ∨ r.red = []) ∧ R is_empty (Ant.diverge ty tr) = r) :=
begin
    unfold R R' map_ant,
    unfold R at h,
    
    cases is_empty ty;
    cases r;
    cases r_acc;
    cases r_inacc;
    cases r_red;
    simp [h, R'._match_1],
end

@[simp]
lemma is_empty_implies_eval_false { is_empty: Gs } { ty: Φ} { env: Env} (h: is_empty.val ty = tt): Φ_eval ty env = ff :=
begin
    have := is_empty.property,
    finish [is_empty_prover],
end

@[simp]
lemma eval_true_imples_empty_false (is_empty: Gs) { ty: Φ } { env: Env } (h: Φ_eval ty env = tt): is_empty.val ty = ff :=
begin
    by_contra,
    have := is_empty.property,
    finish [is_empty_prover],
end

-- (a, i, r) = ℛ is_empty.val (Ant.diverge ant_a ant_tr)
attribute [simp] R map_ant R'
local attribute [simp] ant_eval ant_eval' ant_eval_all

lemma r_correct_1 [decidable_eq Leaf]
    (is_empty: Gs) (gdt: Gdt)
    
    (ant: Ant Φ)
    (h_ant: ant_eval ant = some ∘ gdt_eval gdt)
    
    (env: Env) (leaf: Leaf)
    (h_leaf: gdt_eval gdt env = Result.leaf leaf):

        leaf ∈ (R is_empty.val ant).acc

    :=
begin
    have h: ant_eval ant env = some(Result.leaf leaf), simp [h_ant, h_leaf],
    clear h_ant h_leaf,
    
    induction ant generalizing  env,

    case Ant.leaf {       
        cases c: Φ_eval ant_a env,
        {
            finish,
        },
        {
            have:= eval_true_imples_empty_false is_empty c,
            finish,
        }
    },
    case Ant.branch {
        replace h := ant_eval_branch h,
        cases h,
        case or.inl {
            specialize ant_ih_tr1 env h,
            finish,
        },
        case or.inr {
            specialize ant_ih_tr2 env h,
            finish,
        }
    },
    case Ant.diverge {
        replace h := ant_eval_diverge h,
        let r := R is_empty.val ant_tr,
        have y := R_diverge ant_a (refl r),
        
        cases y,
        {
            cases y with rh y,
            cases y with rs y,
            finish,
        },
        finish,
    }
end




















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
