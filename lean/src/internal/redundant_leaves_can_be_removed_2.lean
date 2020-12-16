import tactic
import ..definitions
import .helper_defs
import data.finset
import .utils
import data.list

variable [GuardModule]
open GuardModule


def Result.is_match : Result → bool
| Result.no_match := ff
| _ := tt

def inactive_leaves' : bool → Gdt → Env → Ant bool
| active (Gdt.leaf leaf) env := Ant.leaf active leaf 
| active (Gdt.branch tr1 tr2) env :=
    Ant.branch 
        (inactive_leaves' (active && (tr1.eval env).is_match) tr1 env)
        (inactive_leaves' (active && !(tr1.eval env).is_match && (tr2.eval env).is_match) tr2 env)
| active (Gdt.grd (Grd.xgrd grd) tr) env :=
    match xgrd_eval grd env with
    | none := inactive_leaves' false tr env
    | some env' := inactive_leaves' active tr env'
    end
| active (Gdt.grd (Grd.bang var) tr) env :=
    if is_bottom var env
    then Ant.diverge active (inactive_leaves' false tr env)
    else Ant.diverge false (inactive_leaves' active tr env)

def inactive_leaves := inactive_leaves' true

lemma inactive_leaves_can_be_removed
    (can_prove_empty: Gs)
    (gdt: Gdt) (gdt_disjoint: gdt.disjoint_leaves)
    -- We only focus on a very particular environment `env`.
    (env: Env)
    
    (leaves: finset Leaf) (leaves_def: leaves ⊆ (R' (inactive_leaves gdt env)).red.to_finset):

        Gdt.eval_option (gdt.remove_leaves leaves) env = gdt.eval env :=
begin
  sorry,
end
#check list.has_subset
def Ant.implies: Ant bool → Ant bool → Prop
| (Ant.branch a_tr1 a_tr2) (Ant.branch b_tr1 b_tr2) := a_tr1.implies b_tr1 ∧ a_tr2.implies b_tr2
| (Ant.diverge a a_tr) (Ant.diverge b b_tr) := (a → b) ∧ a_tr.implies b_tr
| (Ant.leaf a a_leaf) (Ant.leaf b b_leaf) := (a → b) ∧ a_leaf = b_leaf
| _ _ := false

lemma redundant_implies_inactive
    (gdt: Gdt) (can_prove_empty: Gs) (env: Env)
    (ant: Ant Φ) (ant_def: ant.eval_leaves = (A gdt).eval_leaves):
    (ant.map (can_prove_empty.val)).implies (inactive_leaves gdt env) :=
begin
    sorry,
end

lemma sublist_nil_false { α: Type } { a: α } { as: list α }: ¬ a :: as <+ list.nil :=
begin
    by_contra,
    replace a_1 := list.length_le_of_sublist a_1,
    finish,
end

#print prefix list.sublist

lemma bla { α: Type } { la1 la2 lb1 lb2: list α } : (la1 ++ la2).is_nil ↔ la1.is_nil ∧ la2.is_nil :=
begin
    induction la1,
    simp [list.is_nil],
end
 
lemma foo { α: Type } { la1 la2 lb1 lb2: list α } (h1: la1.is_nil → lb1.is_nil) (h2: la2.is_nil → lb2.is_nil):
        (la1 ++ la2).is_nil → (lb1 ++ lb2).is_nil :=
begin
    assume h,
    simp at h,
end

lemma R_monotonous (a: Ant bool) (b: Ant bool) (h: a.implies b): 
        ((R' a).acc.is_nil → (R' b).acc.is_nil) ∧ ((R' a).inacc.is_nil → (R' b).inacc.is_nil) ∧ ((R' a).red <+ (R' b).red) :=
begin
    induction a generalizing b,
    
    case Ant.leaf {
        cases b,
        case Ant.branch { finish [Ant.implies], },
        case Ant.diverge { finish [Ant.implies], },

        cases a_a;
        cases b_a;
        finish [R', Ant.implies, h],
    },

    case Ant.branch {
        cases b,
        case Ant.leaf { finish [Ant.implies], },
        case Ant.diverge { finish [Ant.implies], },

        rw Ant.implies at h,
        cases h,
        specialize a_ih_tr1 b_tr1 h_left,
        specialize a_ih_tr2 b_tr2 h_right,
        
        simp [
            R',
            list.sublist.append a_ih_tr1.2.2 a_ih_tr2.2.2
        ],
    },

    case Ant.diverge {
cases b,
        case Ant.leaf { finish [Ant.implies], },
        case Ant.branch { finish [Ant.implies], },

        rw Ant.implies at h,
        cases h,
        specialize a_ih b_tr h_right,

        split,
        {
            have : ∀ a: bool, ∀ tr: Ant bool, (R' (Ant.diverge a tr)).acc = (R' tr).acc :=
            begin
                assume a tr,
                cases a; cases c1: (R' tr); cases c2: acc; cases c3: inacc; cases c4: red;
                simp [R', c1, c2, c3, c4],
            end,
            simp [this, a_ih],
        },

/-
        unfold R',
        cases R' b_tr,
        cases R' a_tr,
        simp at a_ih,
        cases acc;
        cases inacc;
        cases red;
        cases acc_1;
        cases inacc_1;
        cases red_1;
        simp [sublist_nil_false] at a_ih;
        all_goals {
            try { contradiction, }
        },
        --simp [R'._match_1],

        -/
        have c := R_diverge a_a (refl (R' a_tr)),
        cases c,
        case or.inl {
            cases c with leaf c,
            cases c with rs c,
            cases c with c1 c,
            cases c with c2 c3,

            rw c3,
            simp,

            rw c2 at a_ih,
            simp at a_ih,

            cases b_tr_red: (R' b_tr).red,
            case list.nil {
                simp [sublist_nil_false, b_tr_red] at a_ih,
                contradiction,
            },

            unfold R',
            

            cases R' b_tr,
            simp at a_ih,
            rw a_ih.1,
            rw a_ih.2.1,

            simp at b_tr_red,
            rw b_tr_red,
            
            
            cases b_a;
            simp [R'._match_1],

            simp at c2,
            simp at a_ih,

            rw c2 at a_ih,
            simp at a_ih,
            
            

            unfold R',
            cases (R' b_tr),
            simp at a_ih,

            rw a_ih.1,
            unfold R'._match_1,
        },
        --split c,
        simp at c,


        sorry,

        swap,
        split,

        unfold R',

        cases a_a;
        cases b_a,
        case bool.tt bool.tt { simp [a_ih], },
        case bool.tt bool.ff { finish, },

        case bool.ff bool.ff {
            have c := R_diverge ff (refl (R' a_tr)),
            simp at c,

            cases c,
            case or.inl {

            },

            /-simp [R'],
            cases (R' a_tr),
            cases (R' b_tr),
            simp at a_ih,
            cases acc_1;
            cases red_1;
            cases inacc_1;
            simp [R'._match_1],
            all_goals {
                simp at a_ih,
            },-/
        },

        --simp [a_ih],
    },
end

#print prefix R'._match_1


lemma redundant_leaves_can_be_removed
    (can_prove_empty: Gs)
    (gdt: Gdt) (gdt_disjoint: gdt.disjoint_leaves):
    Gdt.eval_option (gdt.remove_leaves ((R can_prove_empty.val (A gdt)).red.to_finset)) = gdt.eval :=
begin
    ext env:1,

    set leaves := (R' ((A gdt).map can_prove_empty.val)).red.to_finset with leaves_def,

    have : leaves ⊆ (R' (inactive_leaves gdt env)).red.to_finset :=
    begin
        have := redundant_implies_inactive gdt can_prove_empty env (A gdt) (refl ((A gdt).eval_leaves)),
        finish [sublist_subset, R_monotonous],
    end,

    have := inactive_leaves_can_be_removed can_prove_empty gdt gdt_disjoint env leaves this,
    finish,
end
