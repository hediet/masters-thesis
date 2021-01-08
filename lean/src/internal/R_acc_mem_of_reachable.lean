import tactic
import data.finset
import ..definitions
import .internal_definitions
import .tactics
import .utils
import .phi.utils
import .Ant.main
import .Gdt.main
import .U
import .A
import .R
import .R_red_removable

variable [GuardModule]
open GuardModule


lemma gdt_mark_inactive_leaves_inactive_leaves_of_diverged_or_no_match { gdt: Gdt } { env: Env } (gdt_disjoint: gdt.disjoint_leaves):
    (gdt.mark_inactive_leaves env).inactive_leaves = gdt.leaves ↔ gdt.eval env = Result.diverged ∨ gdt.eval env = Result.no_match :=
begin
    induction gdt with leaf generalizing env,
    case Gdt.leaf {
        simp [Gdt.eval, Gdt.mark_inactive_leaves, Ant.inactive_leaves, Gdt.leaves, ne.symm (finset.singleton_ne_empty leaf)],
    },
    case Gdt.grd {
        unfold Gdt.disjoint_leaves at gdt_disjoint,
        cases gdt_grd,
        case Grd.xgrd {
            cases c: xgrd_eval gdt_grd env,
            { simp [Gdt.leaves, Gdt.eval_xgrd_of_none c, Gdt.mark_inactive_leaves, c], },
            { simp [Gdt.leaves, Gdt.eval_xgrd_of_some c, Gdt.mark_inactive_leaves, *], },
        },
        case Grd.bang {
            cases c: is_bottom gdt_grd env,
            { simp [Gdt.leaves, Gdt.eval_bang_of_not_bottom c, Gdt.mark_inactive_leaves, Ant.inactive_leaves, *], },
            { simp [Gdt.leaves, Gdt.eval_bang_of_bottom c, Gdt.mark_inactive_leaves, Ant.inactive_leaves, c], },
        }
    },
    case Gdt.branch {
        unfold Gdt.disjoint_leaves at gdt_disjoint,
        simp [Gdt.mark_inactive_leaves, Ant.inactive_leaves],
        by_cases c: gdt_tr1.eval env = Result.no_match;
        simp [c, Gdt.leaves],
        {
            rw ←gdt_ih_tr2 gdt_disjoint.2.1,
            rw Gdt.mark_inactive_leaves_no_match c,
            rw Gdt.mark_all_leaves_inactive.inactive_leaves,
            have := finset.disjoint_of_subset_right (Gdt.mark_inactive_leaves.inactive_leaves gdt_tr2 env) gdt_disjoint.2.2,
            simp [disjoint_set_union_eq_union_iff_right _ this gdt_disjoint.2.2],
        }, {
            have := finset.disjoint_of_subset_left (Gdt.mark_inactive_leaves.inactive_leaves gdt_tr1 env) gdt_disjoint.2.2,
            simp [disjoint_set_union_eq_union_iff_left _ this gdt_disjoint.2.2, gdt_ih_tr1 gdt_disjoint.1, c],
        }
    },
end


lemma gdt_mark_inactive_leaves_inactive_leaves_of_leaf_match { gdt: Gdt } { env: Env } { leaf: Leaf } (gdt_disjoint: gdt.disjoint_leaves):
    gdt.leaves \ (gdt.mark_inactive_leaves env).inactive_leaves = { leaf } ↔ gdt.eval env = Result.leaf leaf :=
begin
    induction gdt with l generalizing env,
    case Gdt.leaf {
        simp [Gdt.eval, Gdt.mark_inactive_leaves, Ant.inactive_leaves, Gdt.leaves, finset.singleton_inj],
    },
    case Gdt.grd {
        unfold Gdt.disjoint_leaves at gdt_disjoint,
        cases gdt_grd,
        case Grd.xgrd {
            cases c: xgrd_eval gdt_grd env,
            { simp [Gdt.leaves, Gdt.eval_xgrd_of_none c, Gdt.mark_inactive_leaves, c, ne.symm (finset.singleton_ne_empty _)], },
            { simp [Gdt.leaves, Gdt.eval_xgrd_of_some c, Gdt.mark_inactive_leaves, @gdt_ih gdt_disjoint val, *], },
        },
        case Grd.bang {
            cases c: is_bottom gdt_grd env,
            { simp [Gdt.leaves, Gdt.eval_bang_of_not_bottom c, Gdt.mark_inactive_leaves, Ant.inactive_leaves, *], },
            { simp [Gdt.leaves, Gdt.eval_bang_of_bottom c, Gdt.mark_inactive_leaves, Ant.inactive_leaves, c, @gdt_ih gdt_disjoint env, ne.symm (finset.singleton_ne_empty _)], },
        },
    },
    case Gdt.branch {
        unfold Gdt.disjoint_leaves at gdt_disjoint,
        replace gdt_ih_tr1 := λ env, @gdt_ih_tr1 gdt_disjoint.1 env,
        replace gdt_ih_tr2 := λ env, @gdt_ih_tr2 gdt_disjoint.2.1 env,

        simp only [Gdt.leaves, Gdt.mark_inactive_leaves, Ant.inactive_leaves, ne.def],

        have x : (gdt_tr1.mark_inactive_leaves env).inactive_leaves ⊆ gdt_tr1.leaves :=
        begin
            rw ←Gdt.mark_inactive_leaves.leaves,
            exact Ant.inactive_leaves_subset_leaves,
        end,
        have y : (
                if ((gdt_tr1.eval env).is_match)
                then gdt_tr2.mark_all_leaves_inactive
                else (gdt_tr2.mark_inactive_leaves env)
            ).inactive_leaves ⊆ gdt_tr2.leaves := 
        begin
            cases (gdt_tr1.eval env).is_match,
            case bool.ff {
                rw ←Gdt.mark_inactive_leaves.leaves _ env,
                simp only [if_false, bool.coe_sort_ff, Ant.inactive_leaves_subset_leaves],
            },
            case bool.tt {
                rw ←Gdt.mark_all_leaves_inactive.leaves,
                simp only [if_true, bool.coe_sort_tt, Ant.inactive_leaves_subset_leaves],
            },
        end,

        rw disjoint_sets gdt_disjoint.2.2 x y,
        rw Gdt.eval_branch_leaf_iff,
        rw ←gdt_ih_tr2,
        rw ←gdt_ih_tr1,
        
        cases c: (gdt_tr1.eval env).is_match, {
            simp at c,
            simp [c, (gdt_mark_inactive_leaves_inactive_leaves_of_diverged_or_no_match gdt_disjoint.1).2 (or.inr c), ne.symm (finset.singleton_ne_empty _)],
        }, {
            simp at c,
            simp [c],
        }
    },
end

lemma r_correct_1 (ant: Ant bool):
    (R ant).inacc.to_finset ∪ (R ant).red.to_finset ⊆ ant.inactive_leaves :=
begin
    induction ant,
    case Ant.leaf {
        cases c: ant_a;
        simp [R, c, Ant.inactive_leaves],
    },
    case Ant.branch {
        simp [R, Ant.inactive_leaves, *],
        have := finset.union_subset_union ant_ih_tr1 ant_ih_tr2,
        simp [finset.union_comm, finset.union_assoc, finset.union_left_comm] at this,
        exact this,
    },
    case Ant.diverge {
        R_diverge_cases,
        {
            inline R_ant_tr,
            simp [finset.insert_eq] at ant_ih,
            simp [R, Ant.inactive_leaves, ant_ih],
        },
        {
            simp [Ant.inactive_leaves, ant_ih],
        },
    }
end

lemma R_acc_mem_of_reachable { gdt: Gdt } { env: Env } { leaf: Leaf } { ant: Ant Φ }
    (gdt_disjoint: gdt.disjoint_leaves)
    (can_prove_empty: Gs)
    (ant_def: ant.mark_inactive_leaves env = (A gdt).mark_inactive_leaves env)
    (h: gdt.eval env = Result.leaf leaf)
    { r: LeafPartition }
    (r_def: r = R (ant.map can_prove_empty.val)):
    leaf ∈ r.acc \ (r.inacc ++ r.red) :=
begin
    
    have l : leaf ∈ (ant.map can_prove_empty.val).leaves :=
    begin
        
        have : ((A gdt).mark_inactive_leaves env).leaves = (ant.mark_inactive_leaves env).leaves :=
        begin
            simp [ant_def],
        end,
        have : (ant.map can_prove_empty.val).leaves = gdt.leaves := begin
            simp at this,
            simp [this],
        end,
        rw this,
        exact Gdt.leaf_mem_leaves_of_eval_leaf h,
    end,

    have xxx := ant_def,
    rw ←gdt_mark_inactive_leaves_inactive_leaves_of_leaf_match gdt_disjoint at h,
    rw A_mark_inactive_leaves gdt env at ant_def,
    rw ←ant_def at h,


    have leaf_in : leaf ∉ (ant.mark_inactive_leaves env).inactive_leaves :=
    begin
        rw finset.ext_iff at h,
        specialize h leaf,
        simp at h,
        exact h.2,
    end,

    replace leaf_in : leaf ∉ (ant.map can_prove_empty.val).inactive_leaves :=
    begin
        have := can_prove_empty_implies_inactive can_prove_empty ant env,
        replace := (is_redundant_set_monotonous' this).1,
        by_contra,
        have y := this a,
        simp [leaf_in] at y,
        contradiction,
    end,

    have x : leaf ∉ r.inacc ++ r.red :=
    begin
        have := r_correct_1 (ant.map can_prove_empty.val),
        rw finset.subset_iff at this,
        specialize @this leaf,
        rw r_def,
        finish,
    end,
    
    have ant_disjoint: (ant.map can_prove_empty.val).disjoint_leaves := begin
        have x := Ant.disjoint_leaves_of_mark_inactive_leaves_eq xxx,
        have y := Ant.disjoint_leaves_of_gdt_disjoint_leaves gdt_disjoint,
        simp [x, y],
    end,

    have : leaf ∈ r.acc :=
    begin
        
        have : leaf ∈ r.leaves := begin
            rw ←list.mem_to_finset,
            have := @R_leaves_to_finset_eq_leaves _ (ant.map can_prove_empty.val),
            simp only [r_def, this, l],
        end,

        unfold LeafPartition.leaves at this,
        rw list.append_assoc at this,
        rw list.mem_append at this,
        cases this, {
            exact this,
        }, {
            finish [x],
        },
    end,
    
    have acc_no_dup := R_acc_nodup ant_disjoint,
    rw ←r_def at acc_no_dup,
    simp only [has_sdiff.sdiff], 
    rw list.mem_diff_iff_of_nodup acc_no_dup,
    simp [this, x],
end