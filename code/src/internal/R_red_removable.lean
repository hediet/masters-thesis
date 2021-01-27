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

variable [GuardModule]
open GuardModule

lemma R_red_redundant { ant: Ant bool } (ant_disjoint: ant.disjoint_rhss):
    ant.is_redundant_set (R ant).red.to_finset :=
begin
    induction_ant_disjoint ant from ant_disjoint,

    case Ant.rhs {
        unfold Ant.is_redundant_set R,
        cases ant_a;
        simp [Ant.critical_rhs_sets, Ant.inactive_rhss],
    },
    case Ant.branch {
        unfold Ant.is_redundant_set R,
        unfold Ant.is_redundant_set R at ant_ih_tr1,
        unfold Ant.is_redundant_set R at ant_ih_tr2,
        unfold RhsPartition.red,
        split, {
            simp [Ant.inactive_rhss, finset.union_subset_union ant_ih_tr1.1 ant_ih_tr2.1],
            replace ant_ih_tr1 := ant_ih_tr1.1,
            replace ant_ih_tr2 := ant_ih_tr2.1,
            rw subset_inter_subset_subset R_red_subset_rhss at ant_ih_tr1,
            rw subset_inter_subset_subset R_red_subset_rhss at ant_ih_tr2,
            apply subset_inter_subset,
            exact finset.union_subset_union ant_ih_tr1 ant_ih_tr2,
        },

        assume e,
        assume h,
        rw Ant.critical_rhs_sets at h,
        
        replace ant_ih_tr1 := ant_ih_tr1.2,
        replace ant_ih_tr2 := ant_ih_tr2.2,
        simp at h,
        cases h, {
            specialize ant_ih_tr1 e h,
            cases ant_ih_tr1 with x ant_ih_tr1,
            cases ant_ih_tr1 with H ant_ih_tr1,
            
            have : x ∉ (R ant_tr2).red.to_finset :=
            begin
                by_contradiction,
                have h1 := finset.subset_iff.1 (Ant.critical_rhs_set_elements h) H,
                have h2 := finset.subset_iff.1 (R_red_subset_rhss) a,
                have := finset.disjoint_iff_ne.1 ant_disjoint _ h1 _ h2,
                simp at this,
                exact this,
            end,
            use x,
            simp [*],
        },  
        {
            specialize ant_ih_tr2 e h,
            cases ant_ih_tr2 with x ant_ih_tr2,
            cases ant_ih_tr2 with H ant_ih_tr2,
            
            have : x ∉ (R ant_tr1).red.to_finset :=
            begin
                by_contradiction,
                have h1 := finset.subset_iff.1 (Ant.critical_rhs_set_elements h) H,
                have h2 := finset.subset_iff.1 (R_red_subset_rhss) a,
                have := finset.disjoint_iff_ne.1 ant_disjoint _ h2 _ h1,
                simp at this,
                exact this,
            end,
            use x,
            simp [*],
        }
    },
    case Ant.diverge {
        unfold Ant.is_redundant_set,
        unfold Ant.is_redundant_set at ant_ih,
        split, {
            R_diverge_cases,
            {
                inline R_ant_tr,
                unfold RhsPartition.red at *,
                simp only [Ant.inactive_rhss, Ant.rhss_diverge],
                have : rs.to_finset ⊆ (r :: rs).to_finset := by simp [finset.subset_insert],
                have := finset.inter_subset_inter this (finset.subset.refl _),
                exact finset.subset.trans this ant_ih.1,
            },
            {
                exact ant_ih.1,
            },
        },

        assume e,
        assume h,

        unfold Ant.critical_rhs_sets at h,

        R_diverge_cases, {
            inline ant_a,
            simp only [bool.coe_sort_ff, if_false, finset.mem_union, finset.mem_singleton] at h,
            rw R_ant_tr at *,
            unfold RhsPartition.red at *,
            cases h, {
                have := ant_ih.2 e h,
                cases this with x this,
                cases this with H this,
                use x,
                finish,
            }, {
                use r,
                rw h,
                have : r ∈ (R ant_tr).red.to_finset := by simp *,
                have := finset.subset_iff.1 R_red_subset_rhss this,
                split, { exact this, },
                apply R_red_l_not_mem_ls ant_disjoint,
                simp *,
            }
        },
        {
            cases ant_a,
            case bool.tt {
                simp only [if_true, bool.coe_sort_tt, finset.union_empty] at h,
                exact ant_ih.2 e h,
            },

            simp only [bool.coe_sort_ff, if_false, finset.mem_union, finset.mem_singleton] at h,
            cases h, { exact ant_ih.2 e h, },
            rw h,

            cases R_diverge_cases, {
                contradiction,
            },
            cases R_diverge_cases, {
                cases c: (R ant_tr).acc with acc accs, { finish, },
                use acc,
                have acc_mem : acc ∈ (R ant_tr).acc.to_finset := by simp [c],
                simp [finset.subset_iff.1 R_acc_subset_rhss acc_mem, R_acc_l_not_mem_red ant_disjoint c],
            },
            cases R_diverge_cases, {
                cases c: (R ant_tr).inacc with inacc inaccs, { finish, },
                use inacc,
                have inacc_mem : inacc ∈ (R ant_tr).inacc.to_finset := by simp [c],
                simp [finset.subset_iff.1 R_inacc_subset_rhss inacc_mem, R_inacc_l_not_mem_red ant_disjoint c],
            },
            {
                have := Ant.rhss_non_empty ant_tr,
                cases this with l ls,
                rw R_diverge_cases,
                use l,
                simp *,
            }
        },
    },
end

lemma can_prove_empty_implies_inactive (can_prove_empty: CorrectCanProveEmpty) (ant: Ant Φ) (env: Env):
    (ant.map (can_prove_empty.val)) ⟶ (ant.mark_inactive_rhss env) :=
begin
    have : ∀ ty: Φ, (can_prove_empty.val ty) → !ty.eval env := begin
        unfold_coes,
        simp only [bnot_eq_true_eq_eq_ff],
        assume ty h,
        have := can_prove_empty.property,
        finish [correct_can_prove_empty, Φ.is_empty, correct_can_prove_empty],
    end,

    induction ant,
    case Ant.rhs {
        apply Ant.implies.rhs,
        exact this _,
    },
    case Ant.branch {
        simp only [Ant.implies.branch, Ant.map, Ant.mark_inactive_rhss.branch, *],
    },
    case Ant.diverge {
        rw Ant.mark_inactive_rhss_of_diverge,
        apply Ant.implies.diverge ant_ih (this _),
    },
end

lemma A_mark_inactive_rhss (gdt: Gdt) (env: Env): (A gdt).mark_inactive_rhss env = gdt.mark_inactive_rhss env :=
begin
    have : bor ff = id := by refl,
    have : bor tt = λ x, tt := by refl,
    induction gdt generalizing env,
    case Gdt.rhs { refl, },
    case Gdt.branch {
        unfold A,
        rw Ant.mark_inactive_rhss_branch,
        rw Ant.mark_inactive_rhss_of_map_ty_and _ _ _,
        rw [gdt_ih_tr1, gdt_ih_tr2],
        rw U_semantic,
        unfold Gdt.mark_inactive_rhss,
        simp only [true_and, eq_self_iff_true, ne.def, bnot_bnot],
        cases (gdt_tr1.eval env).is_match;
        simp [*, Gdt.mark_inactive_rhss_map_tt],
    },
    case Gdt.grd {
        cases gdt_grd,
        case Grd.xgrd {
            unfold A,
            cases c: xgrd_eval gdt_grd env,
            case option.none {
                rw [Ant.mark_inactive_rhss_of_map_xgrd_in_none c, Gdt.mark_inactive_rhss_of_xgrd_none c],
                rw ←Gdt.mark_inactive_rhss_map_tt _ env,
                rw ←gdt_ih env,
                simp [Ant.mark_inactive_rhss],
            },
            case option.some {
                rw Ant.mark_inactive_rhss_of_map_xgrd_in_some c,
                rw Gdt.mark_inactive_rhss_of_xgrd_some c,
                exact gdt_ih val,
            },
        },
        case Grd.bang {
            unfold A,
            rw Ant.mark_inactive_rhss_of_diverge,
            rw Ant.mark_inactive_rhss_of_map_ty_and,
            rw gdt_ih env,
            unfold Gdt.mark_inactive_rhss,
            cases c: is_bottom gdt_grd env;
            simp [c, *, Gdt.mark_inactive_rhss_map_tt],
        },
    },
end


lemma is_redundant_set_monotonous' { a b: Ant bool } (h: a ⟶ b): 
        a.inactive_rhss ⊆ b.inactive_rhss ∧ b.critical_rhs_sets ⊆ a.critical_rhs_sets :=
begin
    induction a generalizing b;
    cases h with h b_a,
    -- case rhs:
    {
        cases a_a; cases b_a;
        finish [Ant.inactive_rhss, Ant.implies.rhs],
    },
    -- case branch:
    {
        specialize a_ih_tr1 h_h1,
        specialize a_ih_tr2 h_h2,
        simp [ *, finset.union_subset_union, Ant.inactive_rhss, Ant.critical_rhs_sets ],
    },
    -- case grd:
    {
        specialize a_ih h_h1,
        split, { simp [Ant.inactive_rhss, a_ih], },

        cases a_a; cases h_b;
        finish [
            Ant.critical_rhs_sets,
            Ant.implies_same_rhss h_h1,
            finset.union_subset_union,
            a_ih.2,
            subset_right_union
        ],
    },
end

lemma is_redundant_set_monotonous { a b: Ant bool } (rhss: finset Rhs) (h: a ⟶ b):
    a.is_redundant_set rhss → b.is_redundant_set rhss :=
begin
    unfold Ant.is_redundant_set,
    have := is_redundant_set_monotonous' h,
    assume p,
    split,
    {
        rw ←Ant.implies_same_rhss h,
        exact finset.subset.trans p.1 this.1,
    },
    assume e,
    assume q,
    exact p.right e (this.2 q),
end


lemma sets_1 { α: Type } [decidable_eq α] { l1 l2 l3 l4: finset α }
    (h1: l4 ∩ (l1 ∪ l2) ⊆ l1 ∪ l3)
    (h2: disjoint l1 l2)
    : l4 ∩ l2 ⊆ l3 :=
begin
    rw finset.subset_iff,
    simp,
    assume x h3 h4,

    rw finset.subset_iff at h1,
    specialize @h1 x,
    simp at h1,

    simp [finset.disjoint_iff_inter_eq_empty, finset.subset.antisymm_iff, finset.subset_iff] at h2,
    specialize @h2 x,

    tauto, 
end

lemma sets_2 { α: Type } [decidable_eq α] { l1 l2 l3 l4: finset α }
    (h1: l4 ∩ (l1 ∪ l2) ⊆ l3 ∪ l2)
    (h2: disjoint l1 l2)
    : l4 ∩ l1 ⊆ l3 :=
begin
    rw finset.subset_iff,
    simp,
    assume x h3 h4,

    rw finset.subset_iff at h1,
    specialize @h1 x,
    simp at h1,

    simp [finset.disjoint_iff_inter_eq_empty, finset.subset.antisymm_iff, finset.subset_iff] at h2,
    specialize @h2 x,

    tauto, 
end

lemma redundant_rhss_removable
    (gdt: Gdt) (gdt_disjoint: gdt.disjoint_rhss)
    (env: Env)
    (rhss: finset Rhs) (rhss_def: (gdt.mark_inactive_rhss env).is_redundant_set rhss):

        Gdt.eval_option (gdt.remove_rhss rhss) env = gdt.eval env :=
begin
  induction gdt with rhs generalizing env,
  case Gdt.rhs {
      simp [Gdt.eval],
      unfold Gdt.mark_inactive_rhss Ant.is_redundant_set at rhss_def,
      simp [Ant.inactive_rhss, Ant.critical_rhs_sets, Ant.rhss] at rhss_def,
      unfold Gdt.remove_rhss,
      have : ¬rhs ∈ rhss := finset.disjoint_singleton.mp rhss_def,
      simp [this, Gdt.eval_option],
  },

  case Gdt.branch {
        simp [Gdt.mark_inactive_rhss, -Result.is_match_neq_no_match] at rhss_def,
        unfold Gdt.remove_rhss,
        unfold Gdt.disjoint_rhss at gdt_disjoint,

        cases c: (gdt_tr1.eval env).is_match,
        
        case bool.ff {
            rw c at rhss_def,
            simp at c,
            simp only [Ant.inactive_rhss, Ant.is_redundant_set, Ant.critical_rhs_sets, bool.coe_sort_ff, Gdt.mark_inactive_rhss.rhss,
                Ant.rhss_branch, if_false, finset.mem_union, Gdt.mark_inactive_rhss_no_match c, finset.not_mem_empty, false_or,
                Gdt.mark_all_rhss_inactive.critical_rhs_sets, Gdt.mark_all_rhss_inactive.inactive_rhss,
                Gdt.mark_all_rhss_inactive.rhss] at rhss_def,
                            

            have : (gdt_tr1.mark_inactive_rhss env).is_redundant_set rhss :=
            by simp [Gdt.mark_inactive_rhss_no_match c, Gdt.mark_all_rhss_inactive_is_reduntant_set],

            specialize gdt_ih_tr1 gdt_disjoint.1 env this,

            have : (gdt_tr2.mark_inactive_rhss env).is_redundant_set rhss :=
            begin
                have := sets_1 rhss_def.1 gdt_disjoint.2.2,
                unfold Ant.is_redundant_set,
                split, { simp [*], },
                exact rhss_def.2,
            end,

            specialize gdt_ih_tr2 gdt_disjoint.2.1 env this,
            rw ←Gdt.eval_option at gdt_ih_tr2,
            rw Gdt.branch_option_replace_right_env _ (or.intro_left _ gdt_ih_tr2),
            rw ←Gdt.eval_option at gdt_ih_tr1,
            rw Gdt.branch_option_replace_left_env gdt_ih_tr1,
            simp,
        },
        case bool.tt {
            rw c at rhss_def,
            simp only [Result.is_match_tt_neq_no_match, ne.def] at c,
            simp only [Ant.inactive_rhss, Ant.is_redundant_set, Ant.critical_rhs_sets, exists_prop, Gdt.mark_all_rhss_inactive.rhss,
                if_true, bool.coe_sort_tt, Gdt.mark_inactive_rhss.rhss, Ant.rhss_branch, finset.union_empty,
                Gdt.mark_all_rhss_inactive.critical_rhs_sets, Gdt.mark_all_rhss_inactive.inactive_rhss] at rhss_def,
            
            have : (gdt_tr1.mark_inactive_rhss env).is_redundant_set rhss :=
            begin
                unfold Ant.is_redundant_set,
                simp,
                have := sets_2 rhss_def.1 gdt_disjoint.2.2,
                split, { simp [*], },
                exact rhss_def.2,
            end,
            specialize gdt_ih_tr1 gdt_disjoint.1 env this,
            rw ←Gdt.eval_option at c,
            
            rw ←Gdt.eval_option at gdt_ih_tr1,
            rw Gdt.branch_option_replace_left_env gdt_ih_tr1,
            rw Gdt.branch_option_replace_right_env (some gdt_tr2) (or.intro_right _ c),
            simp,
        },
    },

    case Gdt.grd {
        unfold Gdt.disjoint_rhss at gdt_disjoint,
        cases gdt_grd with gdt_grd var,
        case Grd.xgrd {
            cases c: xgrd_eval gdt_grd env with env',
            case option.some {
                simp only [Gdt.eval_xgrd_of_some c],
                unfold Ant.is_redundant_set at rhss_def,
                simp only [Gdt.mark_inactive_rhss, Gdt.mark_inactive_rhss._match_1, c] at rhss_def,
                have : (gdt_tr.mark_inactive_rhss env').is_redundant_set rhss :=
                begin
                    unfold Ant.is_redundant_set,
                    exact rhss_def,
                end,
                
                specialize gdt_ih gdt_disjoint env' this,
                unfold Gdt.remove_rhss,
                rw Gdt.eval_option_of_xgrd_eval_some c,
                exact gdt_ih,
            },
            case option.none {
                simp only [Gdt.eval_xgrd_of_none c],
                unfold Gdt.remove_rhss,
                exact Gdt.eval_option_of_xgrd_eval_none c,
            },
        },
        case Grd.bang {
            cases c: is_bottom var env,
            case bool.tt {
                simp [Gdt.eval_bang_of_bottom c],
                simp only [Ant.is_redundant_set, Ant.inactive_rhss, Ant.critical_rhs_sets, Gdt.mark_inactive_rhss, c,
                    Gdt.mark_all_rhss_inactive.rhss, if_true, Ant.rhss_diverge, finset.empty_union, bool.coe_sort_ff,
                    bool.coe_sort_tt, forall_eq, Gdt.mark_all_rhss_inactive.critical_rhs_sets, if_false, finset.mem_singleton,
                    Gdt.mark_all_rhss_inactive.inactive_rhss] at rhss_def,
                unfold Gdt.remove_rhss,
                apply Gdt.eval_option_of_is_bottom_tt c (Gdt.remove_rhss_neq_none rhss_def.2),
            },
            case bool.ff {
                simp [Ant.is_redundant_set, Gdt.rhss, Gdt.mark_inactive_rhss, c, Ant.inactive_rhss, Ant.critical_rhs_sets] at rhss_def,
                have : (gdt_tr.mark_inactive_rhss env).is_redundant_set rhss, {
                    simp [Ant.is_redundant_set, Gdt.rhss, Gdt.mark_inactive_rhss, c, Ant.inactive_rhss, Ant.critical_rhs_sets],
                    exact rhss_def,
                },
                specialize gdt_ih gdt_disjoint env this,
                unfold Gdt.remove_rhss,
                simp [Gdt.eval_bang_of_not_bottom c],
                rw Gdt.eval_option_of_is_bottom_ff c,
                exact gdt_ih,
            },
        },
    },
end

theorem R_red_removable
    (can_prove_empty: CorrectCanProveEmpty)
    { gdt: Gdt } (gdt_disjoint: gdt.disjoint_rhss)
    { Agdt: Ant Φ }
    (ant_def: Agdt.mark_inactive_rhss = (A gdt).mark_inactive_rhss):
    Gdt.eval_option (gdt.remove_rhss ((R $ Agdt.map can_prove_empty.val).red.to_finset)) = gdt.eval :=
begin
    ext env:1,
    
    -- `Agdt` semantically equals `A gdt`, which represents `gdt` by annotating it with refinement types.
    -- `Agdt` and `A gdt` don't need to be syntactically equal though!
    -- In fact, `𝒜 gdt` and `A gdt` are semantically equal, but not syntactically.

    -- `can_prove_empty` approximates emptiness for a single refinement type.
    -- `ant_empt` approximates emptiness of the refinement types in `Agdt` for every `env`.
    -- It also approximates inactive rhss of `gdt` in context of `env` (ant_empt_imp_gdt).
    let ant_empt := Agdt.map can_prove_empty.val,
    have ant_empt_imp_gdt := calc
        ant_empt ⟶ Agdt.mark_inactive_rhss env : can_prove_empty_implies_inactive can_prove_empty Agdt env
        ...      ⟶ (A gdt).mark_inactive_rhss env : by simp [Ant.implies_refl, ant_def]
        ...      ⟶ gdt.mark_inactive_rhss env : by simp [Ant.implies_refl, A_mark_inactive_rhss gdt env],

    -- Since `gdt` has disjoint rhss, `ant_empt` has disjoint rhss too.
    have ant_empt_disjoint : ant_empt.disjoint_rhss
        := by simp [Ant.disjoint_rhss_of_gdt_disjoint_rhss gdt_disjoint,
                Ant.disjoint_rhss_iff_of_mark_inactive_rhss_eq (function.funext_iff.1 ant_def env)],

    -- The set of rhss `R_red` is redundant in `ant_empt` (red_in_ant_empt).
    -- This means that these rhss are inactive
    -- and not all rhss of possibly active diverge nodes are redundant.
    let R_red := (R ant_empt).red.to_finset,
    have red_in_ant_empt: ant_empt.is_redundant_set R_red := R_red_redundant ant_empt_disjoint,
    
    -- Since `redundant_in` is monotonous and `ant_empt` approximates inactive rhss on `gdt`,
    -- `R_red` is also redundant in `gdt` (red_in_gdt).
    have red_in_gdt: (gdt.mark_inactive_rhss env).is_redundant_set R_red
        := is_redundant_set_monotonous _ ant_empt_imp_gdt red_in_ant_empt,
    
    -- Since `R_red` is a redundant set, it can be removed from `gdt` without
    -- changing the semantics. Note that `R_red` is independent of env.
    show Gdt.eval_option (Gdt.remove_rhss R_red gdt) env = gdt.eval env,
    from redundant_rhss_removable gdt gdt_disjoint env _ red_in_gdt,
end
