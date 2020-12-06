import tactic
import .a_eval_theorem
import .defs
import .helper_defs
import .leaves
import data.finset

variable [GuardModule]
open GuardModule
variable [decidable_eq Leaf]

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
lemma eval_true_implies_empty_false (is_empty: Gs) { ty: Φ } { env: Env } (h: Φ_eval ty env = tt): is_empty.val ty = ff :=
begin
    by_contra,
    have := is_empty.property,
    finish [is_empty_prover],
end

-- (a, i, r) = ℛ is_empty.val (Ant.diverge ant_a ant_tr)
attribute [simp] R map_ant R'
local attribute [simp] ant_eval ant_eval' ant_eval_all

--(gdt: Gdt)
--(h_ant: ant_eval ant = some ∘ gdt_eval gdt)
--(h_leaf: gdt_eval gdt env = Result.leaf leaf):
--have h: ant_eval ant env = some(Result.leaf leaf), simp [h_ant, h_leaf],
    --clear h_ant h_leaf,




lemma r_correct_1
    (is_empty: Gs)    
    (ant: Ant Φ)
    (env: Env) (leaf: Leaf)
    (h: ant_eval ant env = some (Result.leaf leaf)):

        leaf ∈ (R is_empty.val ant).acc
    :=
begin
    induction ant generalizing  env,

    case Ant.leaf {       
        cases c: Φ_eval ant_a env,
        {
            finish,
        },
        {
            have := eval_true_implies_empty_false is_empty c,
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
    },
end

@[simp]
lemma gdt_1 (gdt1: Gdt) (gdt2: Gdt) (env: Env) (h: gdt_eval gdt2 env = Result.no_match):
            gdt_eval (Gdt.branch gdt1 gdt2) env = gdt_eval gdt1 env :=
begin
    rw gdt_eval,
    cases gdt_eval gdt1 env;
    finish,
end

@[simp]
lemma gdtx (gdt1: Gdt) (gdt2: Gdt) (env: Env) (h: gdt_eval gdt1 env = Result.no_match):
            gdt_eval (Gdt.branch gdt1 gdt2) env = gdt_eval gdt2 env :=
begin
    rw gdt_eval,
    cases gdt_eval gdt1 env;
    finish,
end

lemma gdt_match_1_no_match (gdt: Gdt) (env: Env): gdt_eval._match_1 (Result.no_match) (gdt_eval gdt env) = gdt_eval gdt env :=
begin
    cases gdt_eval gdt env;
    finish,
end

@[simp]
lemma gdt_match_branch_match_left (gdt1 gdt2: Gdt) (env: Env) (h: gdt_eval gdt1 env ≠ Result.no_match)
        : gdt_eval (gdt1.branch gdt2) env = gdt_eval gdt1 env :=
begin
    cases c1: gdt_eval gdt1 env;
    cases c2: gdt_eval gdt2 env;
    finish [gdt_eval, gdt_eval._match_1],
end

/-
@[simp]
lemma bla2 (gdt: Gdt) (gdt': Gdt) (env: Env) (h: gdt_eval gdt' env = Result.no_match)
    : gdt_eval._match_1 (gdt_eval gdt env) (gdt_eval gdt' env) = gdt_eval gdt env :=
begin
    cases gdt_eval gdt env;
    finish,
end
-/

lemma gdt_build_branch_replace_left_env { gdt1 gdt1' gdt2: option Gdt } { env: Env }
    (h: gdt_eval_option gdt1 env = gdt_eval_option gdt1' env):
    gdt_eval_option (gdt_build_branch gdt1 gdt2) env = gdt_eval_option (gdt_build_branch gdt1' gdt2) env :=
begin
    cases gdt1;
    cases gdt1';
    cases gdt2;
    
    finish [gdt_build_branch, gdt_eval_option, gdt_eval, gdtx],
end

def 𝒰'option: option Gdt → Φ
| (some gdt) := 𝒰' gdt
| none := Φ.true


lemma gdt_build_branch_replace_right_env { gdt1 gdt2 gdt2': option Gdt } { env: Env }
    (h: (Φ_eval (𝒰'option gdt1) env) → gdt_eval_option gdt2 env = gdt_eval_option gdt2' env):
    gdt_eval_option (gdt_build_branch gdt1 gdt2) env = gdt_eval_option (gdt_build_branch gdt1 gdt2') env :=
begin
    cases gdt1,
    case option.some {

        rw 𝒰'option at h,
        by_cases c: ↥(Φ_eval (𝒰' gdt1) env),
        {
            replace h := h c,
            replace c := 𝒰_eval1.1 c,

            cases gdt2';
            cases gdt2;
            
            all_goals {
                try {
                    simp [gdt_eval_option, gdt_build_branch, 𝒰'option, gdt_eval, gdt_eval._match_1, c],
                },
                try {
                    simp [gdt_eval_option, gdt_build_branch, 𝒰'option, gdt_eval, gdt_eval._match_1, c] at h,
                },
            },
            all_goals {
                exact h,
            },
        },
        {
            replace c := (not_iff_not.2 𝒰_eval1).1 c,
            clear h,

            cases gdt2;
            cases gdt2';


            simp [gdt_build_branch, gdt_eval_option, c],
        }
    },
    case option.none {
        cases gdt2';
        cases gdt2;
        finish [gdt_eval_option, gdt_build_branch, 𝒰'option],
    },
end


lemma inverse_map_ant_leaf { α β: Type } { ant: Ant α } { b: β } { leaf: Leaf } { f: α → β }
    (h: map_ant f ant = Ant.leaf b leaf):
    ∃ a: α, ant = Ant.leaf a leaf ∧ b = f a :=
begin
    cases ant; finish,
end

lemma inverse_map_ant_branch { α β: Type } { ant: Ant α } { a1 a2: Ant β } { f: α → β }
    (h: map_ant f ant = Ant.branch a1 a2):
    ∃ ant1: Ant α, ∃ ant2: Ant α,
        ant = Ant.branch ant1 ant2 ∧ a1 = map_ant f ant1 ∧ a2 = map_ant f ant2 :=
begin
    cases ant,
    case Ant.leaf { finish, },
    case Ant.diverge { finish, },
    case Ant.branch {
        rw map_ant at h,
        use ant_tr1,
        use ant_tr2,
        finish,
    },
end

lemma inverse_map_ant_diverge { α β: Type } { ant: Ant α } { b: β } { a: Ant β } { f: α → β }
    (h: map_ant f ant = Ant.diverge b a):
    ∃ ant_a: α, ∃ ant_ant: Ant α,
        ant = Ant.diverge ant_a ant_ant ∧ b = f ant_a ∧ a = map_ant f ant_ant :=
begin
    cases ant,
    case Ant.leaf { finish, },
    case Ant.diverge {
        rw map_ant at h,
        use ant_a,
        use ant_tr,
        finish,
    },
    case Ant.branch {
        finish,
    },
end

--@[simp]


lemma R_partition { is_empty: Gs } { ant: Ant Φ } { r: LeafPartition } (h: r = R is_empty.val ant):
        ant_leaves ant = r.acc.to_finset ∪ r.inacc.to_finset ∪ r.red.to_finset  :=
begin
    induction ant generalizing r,
    case Ant.leaf {
        simp [ant_leaves, R, map_ant, R'] at h,
        cases c: is_empty.val ant_a, {
            simp at c,
            simp [c] at h,
            rw h,
            simp [ant_leaves],
        }, {
            simp at c,
            simp [c] at h,
            rw h,
            simp [ant_leaves],
        },
    },
    case Ant.branch {
        rw ant_leaves,
        rw [R, map_ant, R'] at h,

        set r1 := R is_empty.val ant_tr1,
        set r2 := R is_empty.val ant_tr2,
        replace hr : r = {acc := r1.acc ++ r2.acc, inacc := r1.inacc ++ r2.inacc, red := r1.red ++ r2.red} := h,

        specialize ant_ih_tr1 (refl r1),
        rw ant_ih_tr1,

        specialize ant_ih_tr2 (refl r2),
        rw ant_ih_tr2,
        rw hr,

        simp [finset.union_comm, finset.union_assoc, finset.union_left_comm, to_finset_append],
    },
    case Ant.diverge {
        rw ant_leaves,
        set r2 := R is_empty.val ant_tr with r2_def,
        specialize ant_ih (refl r2),
        
        let r := R is_empty.val ant_tr,
        have y := R_diverge ant_a (refl r),
        cases y,
        {
            cases y with rh y,
            cases y with rs y,
            cases y with y1 y,
            
            finish,
        },
        {
            cases y with y1 y,
            finish,
        }
    },
end

lemma ant_eval_all_assume_uncovered (gdt: Gdt) (ant: Ant Φ) (env: Env)
    (h: Φ_eval (𝒰' gdt) env = tt):
    ant_eval_all (map_ant (𝒰' gdt).and ant) env = ant_eval_all ant env :=
begin
    rw ant_eval_all,
    rw map_ant_associative,
    rw function.comp,
    unfold Φ_eval,
    rw h,
    simp,
end

/-
@[simp]
lemma true_is_not_empty { is_empty: Gs }: is_empty.val Φ.true = ff :=
begin
    have: Φ_eval Φ.true (@default Env Env_inhabited) = tt, { rw Φ_eval, },
    exact eval_true_implies_empty_false is_empty this,
end
-/

@[simp]
lemma true_eval_true { env: Env } : Φ_eval Φ.true env = tt :=
begin
    simp [Φ_eval],
end



lemma grd_eval_xgrd_some { grd: XGrd } { tr: Gdt } { env env': Env }
    (h: xgrd_eval grd env = some env'):
    gdt_eval (Gdt.grd (Grd.xgrd grd) tr) env = gdt_eval tr env' :=
begin
    simp [gdt_eval, h],
end

lemma grd_eval_xgrd_none { grd: XGrd } { tr: Gdt } { env: Env }
    (h: xgrd_eval grd env = none):
    gdt_eval (Gdt.grd (Grd.xgrd grd) tr) env = Result.no_match :=
begin
    simp [gdt_eval, h],
end

lemma grd_eval_option_xgrd_some { grd: XGrd } { tr: option Gdt } { env env': Env }
    (h: xgrd_eval grd env = some env'):
    gdt_eval_option (gdt_build_grd (Grd.xgrd grd) tr) env = gdt_eval_option tr env' :=
begin
    cases tr;
    simp [gdt_eval_option, gdt_build_grd, gdt_eval, h],
end

lemma grd_eval_option_xgrd_none { grd: XGrd } { tr: option Gdt } { env }
    (h: xgrd_eval grd env = none):
    gdt_eval_option (gdt_build_grd (Grd.xgrd grd) tr) env = Result.no_match :=
begin
    cases tr;
    simp [gdt_eval_option, gdt_build_grd, gdt_eval, h],
end

lemma grd_eval_bang_is_not_bottom { tr: Gdt } { env: Env } { var: Var }
    (h: is_bottom var env = ff):
    gdt_eval (Gdt.grd (Grd.bang var) tr) env = gdt_eval tr env :=
begin
    simp [gdt_eval, h],
end

lemma grd_eval_bang_is_bottom { tr: Gdt } { env: Env } { var: Var }
    (h: is_bottom var env = tt):
    gdt_eval (Gdt.grd (Grd.bang var) tr) env = Result.diverged :=
begin
    simp [gdt_eval, h],
end

lemma grd_eval_option_bang_is_not_bottom { tr: option Gdt } { env: Env } { var: Var }
    (h: is_bottom var env = ff):
    gdt_eval_option (gdt_build_grd (Grd.bang var) tr) env = gdt_eval_option tr env :=
begin
    cases tr;
    simp [gdt_eval, gdt_eval_option, gdt_build_grd, h],
end

lemma grd_eval_option_bang_is_bottom { tr: option Gdt } { env: Env } { var: Var }
    (h: is_bottom var env = tt):
    gdt_eval_option (gdt_build_grd (Grd.bang var) tr) env =
        if tr.is_some then Result.diverged else Result.no_match :=
begin
    cases tr;
    simp [gdt_eval, gdt_eval_option, gdt_build_grd, h],
end


lemma r_correct_2
    (is_empty: Gs)
    (gdt: Gdt) (gdt_disjoint: disjoint_leaves gdt)
    (env ant_env: Env)
    (ant: Ant Φ) (ant_def: ant_eval_all ant ant_env = ant_eval_all (𝒜' gdt) env)
    (r: LeafPartition) (r_def: r = R is_empty.val ant):

        gdt_eval_option (gdt_remove_leaves r.red.to_finset gdt) env = gdt_eval gdt env :=
begin
    induction gdt generalizing r ant env ant_env,


    case Gdt.grd {
        rw disjoint_leaves at gdt_disjoint,
        replace gdt_ih := gdt_ih gdt_disjoint,
        clear gdt_disjoint,

        cases gdt_grd,

        case Grd.xgrd {

            rw [𝒜'] at ant_def,
            
            cases c: xgrd_eval gdt_grd env with env',

            case option.some {
                -- todo
                unfold ant_eval_all at ant_def,
                rw map_ant_associative at ant_def,
                rw function.comp at ant_def,
                unfold Φ_eval at ant_def,
                rw c at ant_def,
                unfold Φ_eval._match_1 at ant_def,
                rw ←ant_eval_all at ant_def,
                rw ←ant_eval_all at ant_def,
                
                specialize gdt_ih r ant env' ant_env ant_def r_def,
                
                
                rw [gdt_remove_leaves, grd_eval_xgrd_some c, grd_eval_option_xgrd_some c],
                exact gdt_ih,
            },

            case option.none {
                rw [gdt_remove_leaves, grd_eval_option_xgrd_none c, grd_eval_xgrd_none c],
            },
        },

        case Grd.bang {
            rw [𝒜'] at ant_def,
            unfold ant_eval_all at ant_def,
            unfold map_ant at ant_def,
            rw ←ant_eval_all at ant_def,
            rw map_ant_associative at ant_def,
            rw function.comp at ant_def,
            unfold Φ_eval at ant_def,

            
            
            replace ant_def := inverse_map_ant_diverge ant_def,
            cases ant_def with ant_a ant_def,
            cases ant_def with ant_ant ant_def,
            cases ant_def with ant_def ant_h1,
            cases ant_h1 with ant_h1 ant_h2,

            simp at ant_h1,

            rw ant_def at r_def,
            --rw R at r_def,
            --rw map_ant at r_def,
            --rw R' at r_def,
            --rw ←R at r_def,

            cases c: is_bottom gdt_grd env,
            case bool.ff {
                rw c at ant_h2,
                simp at ant_h2,
                rw ←ant_eval_all at ant_h2,
                rw ←ant_eval_all at ant_h2,

                
                set r' := R is_empty.val ant_ant with r'_def,


                specialize gdt_ih r' ant_ant env ant_env (eq.symm ant_h2) r'_def,


                have y := R_diverge ant_a (eq.symm r'_def),

                cases y,
                case or.inl {
                    cases y with hr y,
                    cases y with rs y,
                    cases y with y1 y,
                    cases y with y2 y,
                    rw y at r_def,
                    rw r_def,
                    simp,
                    rw y2 at gdt_ih,
                    simp at gdt_ih,
                    rw grd_eval_bang_is_not_bottom c,
                    rw ←gdt_ih,
                    rw gdt_remove_leaves,
                    rw grd_eval_option_bang_is_not_bottom c,
                    sorry,
                },

                case or.inr {
                    cases y with y1 y,
                    rw y at r_def,
                    rw ← r_def at gdt_ih,
                    rw grd_eval_bang_is_not_bottom c,
                    rw gdt_remove_leaves,
                    rw grd_eval_option_bang_is_not_bottom c,
                    exact gdt_ih,
                },
            },

            case bool.tt {
                rw c at ant_h2,
                simp at ant_h2,

                set r' := R is_empty.val ant_ant with r'_def,

                rw grd_eval_bang_is_bottom c,

                have y := R_diverge ant_a (eq.symm r'_def),

                rw gdt_remove_leaves,
                rw grd_eval_option_bang_is_bottom c,

                suffices : (gdt_remove_leaves r.red.to_finset gdt_tr).is_some = tt,
                simp [this],

                cases y,

                case or.inl {
                    cases y with hr y,
                    cases y with rs y,
                    cases y with y1 y,
                    cases y with y2 y,
                    sorry,
                },

                case or.inr {
                    cases y with y1 y,
                    rw y at r_def,
                    rw r_def,
                    cases y1 with x y,
                    rw c at ant_h1,
                    finish [is_empty_implies_eval_false x],
                    sorry,
                }

                -- to show: ∃ x ∈ gdt_leaves ant_grd \ r.red 
            },

            
        },
    },


    case Gdt.leaf {
        simp [gdt_eval],
        simp [𝒜', map_ant] at ant_def,
        
        have ha := inverse_map_ant_leaf ant_def,
        cases ha with ty ha,
        cases ha with ha1 ha2,
        rw ha1 at r_def,
        rw R at r_def,
        rw map_ant at r_def,
        rw R' at r_def,

        cases c: is_empty.val ty,
        { simp [r_def, gdt_eval_option, gdt_eval, c], },
        { finish [is_empty_implies_eval_false c], },
    },

    case Gdt.branch {
        -- branch to top


        have ha := ant_def,
        have hr := r_def,
        have d := gdt_disjoint,

        rw 𝒜' at ha,
        rw ant_eval_all at ha,
        rw ant_eval_all at ha,
        rw map_ant at ha,
        rw ←ant_eval_all at ha,
        rw ←ant_eval_all at ha,
        rw ←ant_eval_all at ha,

        replace ha := inverse_map_ant_branch ha,
        cases ha with ant1 ha,
        cases ha with ant2 ha,
        cases ha with ha1 ha,
        cases ha with ha2 ha3,
        rw ←ant_eval_all at ha2,
        rw ←ant_eval_all at ha3,


        rw ha1 at hr,
        rw R at hr,
        rw map_ant at hr,
        rw R' at hr,
        
        set r1 := R' (map_ant is_empty.val ant1) with r1_eq,
        set r2 := R' (map_ant is_empty.val ant2) with r2_eq,
        replace hr : r = {acc := r1.acc ++ r2.acc, inacc := r1.inacc ++ r2.inacc, red := r1.red ++ r2.red} := hr,
        
        rw disjoint_leaves at d,
        cases d with d_tr1 d,
        cases d with d_tr2 d,
        

        specialize gdt_ih_tr1 d_tr1 r1 ant1 env ant_env,
        replace gdt_ih_tr1 := gdt_ih_tr1 (eq.symm ha2) r1_eq,


        rw gdt_remove_leaves,
 
        have grd1_ant1_leaves_eq: ant_leaves ant1 = gdt_leaves gdt_tr1, {
            rw ←map_leaves_id _ (λ ty, Φ_eval ty ant_env),
            rw ←ant_eval_all,
            rw ←ha2,
            simp [gdt_leaves_eq_ant_leaves, map_leaves_id, ant_eval_all],
        },

        
        


        have: gdt_remove_leaves r.red.to_finset gdt_tr1 = gdt_remove_leaves r1.red.to_finset gdt_tr1, {
            rw hr,
            simp [to_finset_append],

            have: r2.red.to_finset ⊆ ant_leaves ant2, {
                have x : r2.acc.to_finset ∪ r2.inacc.to_finset ∪ r2.red.to_finset =
                        r2.red.to_finset ∪ r2.acc.to_finset ∪ r2.inacc.to_finset, {
                    simp [finset.union_comm, finset.union_assoc, finset.union_left_comm, to_finset_append],
                },
                simp [r2.red.to_finset.subset_union_left, R_partition r2_eq, x],
            },
            have grd2_ant2_leaves_eq: ant_leaves ant2 = gdt_leaves gdt_tr2, {
                rw ←map_leaves_id _ (λ ty, Φ_eval ty ant_env),
                rw ←ant_eval_all,
                rw ←ha3,
                simp [gdt_leaves_eq_ant_leaves, map_leaves_id, ant_eval_all],
            },
            rw grd2_ant2_leaves_eq at this,

            have: disjoint (gdt_leaves gdt_tr1) r2.red.to_finset, {
                exact finset.disjoint_of_subset_right this d,
            },

            have: (r1.red.to_finset ∪ r2.red.to_finset) ∩ gdt_leaves gdt_tr1 = r1.red.to_finset ∩ gdt_leaves gdt_tr1, {
                rw finset.inter_distrib_right, --(gdt_leaves gdt_tr1) r1.red.to_finset r2.red.to_finset,
                rw finset.disjoint_iff_inter_eq_empty at this,
                rw finset.inter_comm at this,
                simp [this],
            },
            
            rw gdt_remove_leaves_intersect,
            simp [this, ←gdt_remove_leaves_intersect],
        },

        rw this,

        have: gdt_eval gdt_tr1 env = gdt_eval_option (some gdt_tr1) env, { simp [gdt_eval_option], },

        rw this at gdt_ih_tr1,

        rw gdt_build_branch_replace_left_env gdt_ih_tr1,

        clear gdt_ih_tr1,
        clear this,
        clear this,
        clear d_tr1,


        


        have p: (Φ_eval (𝒰'option (some gdt_tr1)) env) →
            gdt_eval_option (gdt_remove_leaves r.red.to_finset gdt_tr2) env = gdt_eval_option (some gdt_tr2) env :=
        begin
            assume p,
            rw 𝒰'option at p,
            rw ant_eval_all at ha3,
            rw map_ant_associative at ha3,
            rw function.comp at ha3,
            unfold Φ_eval at ha3,

            replace p : Φ_eval (𝒰' gdt_tr1) env = tt, exact p,
            
            rw p at ha3,
            simp at ha3,
            rw ←ant_eval_all at ha3,
            rw ←ant_eval_all at ha3,
            rw ←R at r2_eq,
            specialize gdt_ih_tr2 d_tr2 r2 ant2 env ant_env,
            replace gdt_ih_tr2 := gdt_ih_tr2 (eq.symm ha3) r2_eq,
            rw gdt_eval_option,
            rw ← gdt_ih_tr2,
            
            have: gdt_remove_leaves r.red.to_finset gdt_tr2 = gdt_remove_leaves r2.red.to_finset gdt_tr2, {
                rw hr,
                simp [to_finset_append],

                have: r1.red.to_finset ⊆ ant_leaves ant1, {
                    have x : r1.acc.to_finset ∪ r1.inacc.to_finset ∪ r1.red.to_finset =
                            r1.red.to_finset ∪ r1.acc.to_finset ∪ r1.inacc.to_finset, {
                        simp [finset.union_comm, finset.union_assoc, finset.union_left_comm, to_finset_append],
                    },
                    simp [r1.red.to_finset.subset_union_left, R_partition r1_eq, x],
                },
                have grd1_ant1_leaves_eq: ant_leaves ant1 = gdt_leaves gdt_tr1, {
                    rw ←map_leaves_id _ (λ ty, Φ_eval ty ant_env),
                    rw ←ant_eval_all,
                    rw ←ha2,
                    simp [gdt_leaves_eq_ant_leaves, map_leaves_id, ant_eval_all],
                },
                rw grd1_ant1_leaves_eq at this,

                have: disjoint (gdt_leaves gdt_tr2) r1.red.to_finset, {
                    replace d := disjoint.symm d,
                    exact finset.disjoint_of_subset_right this d,
                },

                have: (r1.red.to_finset ∪ r2.red.to_finset) ∩ gdt_leaves gdt_tr2 = r2.red.to_finset ∩ gdt_leaves gdt_tr2, {
                    rw finset.inter_distrib_right, --(gdt_leaves gdt_tr1) r1.red.to_finset r2.red.to_finset,
                    rw finset.disjoint_iff_inter_eq_empty at this,
                    rw finset.inter_comm at this,
                    simp [this],
                },
                
                rw gdt_remove_leaves_intersect,
                simp [this, ←gdt_remove_leaves_intersect],
            },
            rw this,
        end,

        rw gdt_build_branch_replace_right_env p,
        simp [gdt_build_branch, gdt_eval_option],
    },
end














-- Every redundant leaf can be marked as inaccessible instead and
-- every inaccessible leaf can be marked as accessible instead without invalidating the theorem. This only weakens the analysis.

theorem r_correct : ∀ gdt: Gdt, ∀ is_empty: Gs,
    (
        -- structure + später matchen
        let ⟨ a, i, r ⟩ := ℛ is_empty.val $ 𝒜 gdt
        in
                -- Leaves that are redundant and neither accessible nor inaccessible can be removed without changing semantics.
                -- If all leaves are unique, a, i and r are disjoint.
                -- In that case, `r.remove_all (i ++ a)` = `r`.
                -- If all leaves are equal, `r.remove_all (i ++ a)` usually is the empty list.
                gdt_eval_option (gdt_remove_leaves (r.remove_all (i ++ a)) gdt)
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
