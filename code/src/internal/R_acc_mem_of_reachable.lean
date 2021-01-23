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


lemma gdt_mark_inactive_rhss_inactive_rhss_of_diverged_or_no_match { gdt: Gdt } { env: Env } (gdt_disjoint: gdt.disjoint_rhss):
    (gdt.mark_inactive_rhss env).inactive_rhss = gdt.rhss ↔ gdt.eval env = Result.diverged ∨ gdt.eval env = Result.no_match :=
begin
    induction gdt with rhs generalizing env,
    case Gdt.rhs {
        simp [Gdt.eval, Gdt.mark_inactive_rhss, Ant.inactive_rhss, Gdt.rhss, ne.symm (finset.singleton_ne_empty rhs)],
    },
    case Gdt.grd {
        unfold Gdt.disjoint_rhss at gdt_disjoint,
        cases gdt_grd,
        case Grd.xgrd {
            cases c: xgrd_eval gdt_grd env,
            { simp [Gdt.rhss, Gdt.eval_xgrd_of_none c, Gdt.mark_inactive_rhss, c], },
            { simp [Gdt.rhss, Gdt.eval_xgrd_of_some c, Gdt.mark_inactive_rhss, *], },
        },
        case Grd.bang {
            cases c: is_bottom gdt_grd env,
            { simp [Gdt.rhss, Gdt.eval_bang_of_not_bottom c, Gdt.mark_inactive_rhss, Ant.inactive_rhss, *], },
            { simp [Gdt.rhss, Gdt.eval_bang_of_bottom c, Gdt.mark_inactive_rhss, Ant.inactive_rhss, c], },
        }
    },
    case Gdt.branch {
        unfold Gdt.disjoint_rhss at gdt_disjoint,
        simp [Gdt.mark_inactive_rhss, Ant.inactive_rhss],
        by_cases c: gdt_tr1.eval env = Result.no_match;
        simp [c, Gdt.rhss],
        {
            rw ←gdt_ih_tr2 gdt_disjoint.2.1,
            rw Gdt.mark_inactive_rhss_no_match c,
            rw Gdt.mark_all_rhss_inactive.inactive_rhss,
            have := finset.disjoint_of_subset_right (Gdt.mark_inactive_rhss.inactive_rhss gdt_tr2 env) gdt_disjoint.2.2,
            simp [disjoint_set_union_eq_union_iff_right _ this gdt_disjoint.2.2],
        }, {
            have := finset.disjoint_of_subset_left (Gdt.mark_inactive_rhss.inactive_rhss gdt_tr1 env) gdt_disjoint.2.2,
            simp [disjoint_set_union_eq_union_iff_left _ this gdt_disjoint.2.2, gdt_ih_tr1 gdt_disjoint.1, c],
        }
    },
end


lemma gdt_mark_inactive_rhss_inactive_rhss_of_rhs_match { gdt: Gdt } { env: Env } { rhs: Rhs } (gdt_disjoint: gdt.disjoint_rhss):
    gdt.rhss \ (gdt.mark_inactive_rhss env).inactive_rhss = { rhs } ↔ gdt.eval env = Result.value rhs :=
begin
    induction gdt with l generalizing env,
    case Gdt.rhs {
        simp [Gdt.eval, Gdt.mark_inactive_rhss, Ant.inactive_rhss, Gdt.rhss, finset.singleton_inj],
    },
    case Gdt.grd {
        unfold Gdt.disjoint_rhss at gdt_disjoint,
        cases gdt_grd,
        case Grd.xgrd {
            cases c: xgrd_eval gdt_grd env,
            { simp [Gdt.rhss, Gdt.eval_xgrd_of_none c, Gdt.mark_inactive_rhss, c, ne.symm (finset.singleton_ne_empty _)], },
            { simp [Gdt.rhss, Gdt.eval_xgrd_of_some c, Gdt.mark_inactive_rhss, @gdt_ih gdt_disjoint val, *], },
        },
        case Grd.bang {
            cases c: is_bottom gdt_grd env,
            { simp [Gdt.rhss, Gdt.eval_bang_of_not_bottom c, Gdt.mark_inactive_rhss, Ant.inactive_rhss, *], },
            { simp [Gdt.rhss, Gdt.eval_bang_of_bottom c, Gdt.mark_inactive_rhss, Ant.inactive_rhss, c, @gdt_ih gdt_disjoint env, ne.symm (finset.singleton_ne_empty _)], },
        },
    },
    case Gdt.branch {
        unfold Gdt.disjoint_rhss at gdt_disjoint,
        replace gdt_ih_tr1 := λ env, @gdt_ih_tr1 gdt_disjoint.1 env,
        replace gdt_ih_tr2 := λ env, @gdt_ih_tr2 gdt_disjoint.2.1 env,

        simp only [Gdt.rhss, Gdt.mark_inactive_rhss, Ant.inactive_rhss, ne.def],

        have x : (gdt_tr1.mark_inactive_rhss env).inactive_rhss ⊆ gdt_tr1.rhss :=
        begin
            rw ←Gdt.mark_inactive_rhss.rhss,
            exact Ant.inactive_rhss_subset_rhss,
        end,
        have y : (
                if ((gdt_tr1.eval env).is_match)
                then gdt_tr2.mark_all_rhss_inactive
                else (gdt_tr2.mark_inactive_rhss env)
            ).inactive_rhss ⊆ gdt_tr2.rhss := 
        begin
            cases (gdt_tr1.eval env).is_match,
            case bool.ff {
                rw ←Gdt.mark_inactive_rhss.rhss _ env,
                simp only [if_false, bool.coe_sort_ff, Ant.inactive_rhss_subset_rhss],
            },
            case bool.tt {
                rw ←Gdt.mark_all_rhss_inactive.rhss,
                simp only [if_true, bool.coe_sort_tt, Ant.inactive_rhss_subset_rhss],
            },
        end,

        rw disjoint_sets gdt_disjoint.2.2 x y,
        rw Gdt.eval_branch_rhs_iff,
        rw ←gdt_ih_tr2,
        rw ←gdt_ih_tr1,
        
        cases c: (gdt_tr1.eval env).is_match, {
            simp at c,
            simp [c, (gdt_mark_inactive_rhss_inactive_rhss_of_diverged_or_no_match gdt_disjoint.1).2 (or.inr c), ne.symm (finset.singleton_ne_empty _)],
        }, {
            simp at c,
            simp [c],
        }
    },
end

lemma r_correct_1 (ant: Ant bool):
    (R ant).inacc.to_finset ∪ (R ant).red.to_finset ⊆ ant.inactive_rhss :=
begin
    induction ant,
    case Ant.rhs {
        cases c: ant_a;
        simp [R, c, Ant.inactive_rhss],
    },
    case Ant.branch {
        simp [R, Ant.inactive_rhss, *],
        have := finset.union_subset_union ant_ih_tr1 ant_ih_tr2,
        simp [finset.union_comm, finset.union_assoc, finset.union_left_comm] at this,
        exact this,
    },
    case Ant.diverge {
        R_diverge_cases,
        {
            inline R_ant_tr,
            simp [finset.insert_eq] at ant_ih,
            simp [R, Ant.inactive_rhss, ant_ih],
        },
        {
            simp [Ant.inactive_rhss, ant_ih],
        },
    }
end

lemma R_acc_mem_of_reachable { gdt: Gdt } { env: Env } { rhs: Rhs } { ant: Ant Φ }
    (gdt_disjoint: gdt.disjoint_rhss)
    (can_prove_empty: Gs)
    (ant_def: ant.mark_inactive_rhss env = (A gdt).mark_inactive_rhss env)
    (h: gdt.eval env = Result.value rhs)
    { r: RhsPartition }
    (r_def: r = R (ant.map can_prove_empty.val)):
    rhs ∈ r.acc \ (r.inacc ++ r.red) :=
begin
    
    have l : rhs ∈ (ant.map can_prove_empty.val).rhss :=
    begin
        
        have : ((A gdt).mark_inactive_rhss env).rhss = (ant.mark_inactive_rhss env).rhss :=
        begin
            simp [ant_def],
        end,
        have : (ant.map can_prove_empty.val).rhss = gdt.rhss := begin
            simp at this,
            simp [this],
        end,
        rw this,
        exact Gdt.rhs_mem_rhss_of_eval_rhs h,
    end,

    have xxx := ant_def,
    rw ←gdt_mark_inactive_rhss_inactive_rhss_of_rhs_match gdt_disjoint at h,
    rw A_mark_inactive_rhss gdt env at ant_def,
    rw ←ant_def at h,


    have rhs_in : rhs ∉ (ant.mark_inactive_rhss env).inactive_rhss :=
    begin
        rw finset.ext_iff at h,
        specialize h rhs,
        simp at h,
        exact h.2,
    end,

    replace rhs_in : rhs ∉ (ant.map can_prove_empty.val).inactive_rhss :=
    begin
        have := can_prove_empty_implies_inactive can_prove_empty ant env,
        replace := (is_redundant_set_monotonous' this).1,
        by_contra,
        have y := this a,
        simp [rhs_in] at y,
        contradiction,
    end,

    have x : rhs ∉ r.inacc ++ r.red :=
    begin
        have := r_correct_1 (ant.map can_prove_empty.val),
        rw finset.subset_iff at this,
        specialize @this rhs,
        rw r_def,
        finish,
    end,
    
    have ant_disjoint: (ant.map can_prove_empty.val).disjoint_rhss := begin
        have x := Ant.disjoint_rhss_of_mark_inactive_rhss_eq xxx,
        have y := Ant.disjoint_rhss_of_gdt_disjoint_rhss gdt_disjoint,
        simp [x, y],
    end,

    have : rhs ∈ r.acc :=
    begin
        
        have : rhs ∈ r.rhss := begin
            rw ←list.mem_to_finset,
            have := @R_rhss_to_finset_eq_rhss _ (ant.map can_prove_empty.val),
            simp only [r_def, this, l],
        end,

        unfold RhsPartition.rhss at this,
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