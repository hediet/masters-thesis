import tactic
import data.finset
import data.list
import data.bool
import ...definitions
import ..helper_defs
import ..utils
import ..leaves_theory
import .ant_implies
import .inactive
import ..U_semantic

variable [GuardModule]
open GuardModule


def Ant.mark_inactive_leaves (ant: Ant Φ) (env: Env) := ant.map (λ ty, !(ty.eval env))

@[simp]
lemma Ant.mark_inactive_leaves.branch (ant1 ant2: Ant Φ) (env) :
    (ant1.branch ant2).mark_inactive_leaves env = (ant1.mark_inactive_leaves env).branch (ant2.mark_inactive_leaves env) :=
by simp [Ant.map, Ant.mark_inactive_leaves]

@[simp]
lemma Ant.mark_inactive_leaves.diverge (a) (ant: Ant Φ) (env) :
    (Ant.diverge a ant).mark_inactive_leaves env = Ant.diverge (!(a.eval env)) (ant.mark_inactive_leaves env) :=
by simp [Ant.map, Ant.mark_inactive_leaves]

lemma can_prove_empty_implies_inactive (can_prove_empty: Gs) (ant: Ant Φ) (env: Env):
    (ant.map (can_prove_empty.val)) ⟶ (ant.mark_inactive_leaves env) :=
begin
    induction ant,
    case Ant.leaf {
        unfold Ant.map Ant.mark_inactive_leaves,
        apply Ant.implies.leaf,
        -- TODO WTF
        unfold_coes,
        simp,
        unfold_coes,
        apply is_empty_implies_eval_false,
    },
    case Ant.branch {
        -- TODO only is required here
        simp only [Ant.implies.branch, Ant.map, *, Ant.mark_inactive_leaves.branch],
    },
    case Ant.diverge {
        unfold Ant.map,
        rw Ant.mark_inactive_leaves.diverge,
        apply Ant.implies.diverge,
        { exact ant_ih, },
        {
            -- TODO can this be improved?
            have := @is_empty_implies_eval_false _ can_prove_empty ant_a env,
            unfold_coes,
            finish,
        }
    },
end

lemma A_mark_inactive_leaves (gdt: Gdt) (env: Env): (A gdt).mark_inactive_leaves env = gdt.mark_inactive_leaves env :=
begin
    induction gdt generalizing env,
    case Gdt.leaf {
        simp [A, Ant.mark_inactive_leaves, Ant.map, Φ.eval, Gdt.mark_inactive_leaves],
    },
    case Gdt.branch {
        unfold A Ant.mark_inactive_leaves Ant.map Gdt.mark_inactive_leaves,
        rw Ant.map.associative,
        rw function.comp,
        unfold Φ.eval,
        rw U_semantic,

        cases c: (gdt_tr1.eval env).is_match,
        case bool.ff {
            specialize gdt_ih_tr1 env,
            unfold Ant.mark_inactive_leaves at gdt_ih_tr1,
            specialize gdt_ih_tr2 env,
            unfold Ant.mark_inactive_leaves at gdt_ih_tr2,
            
            simp [c, ←Gdt.mark_inactive_leaves_no_match, *],
        },

        case bool.tt {
            have : (A gdt_tr2).map (λ (x : Φ), !(!tt && x.eval env)) =
                    (((A gdt_tr2).mark_inactive_leaves env).map (λ x, tt)) := 
            begin
                simp [Ant.mark_inactive_leaves, Ant.map.associative, function.comp],
            end,
            rw this,
            specialize gdt_ih_tr2 env,
            rw gdt_ih_tr2,
            specialize gdt_ih_tr1 env,
            unfold Ant.mark_inactive_leaves at gdt_ih_tr1,
            simp [Gdt.mark_inactive_leaves_mark_all_leaves_inactive, *],
        },
    },
    case Gdt.grd {
        cases gdt_grd,
        case Grd.xgrd {
            unfold A Ant.map,
            unfold Ant.mark_inactive_leaves,
            rw Ant.map.associative,
            rw function.comp,
            unfold Φ.eval,

            unfold Gdt.mark_inactive_leaves,

            cases xgrd_eval gdt_grd env;

            unfold Gdt.mark_inactive_leaves._match_1;
            unfold Φ.eval._match_1,

            {
                have := Gdt.mark_inactive_leaves_mark_all_leaves_inactive gdt_tr env,
                rw ←gdt_ih at this,
                rw Ant.mark_inactive_leaves at this,
                rw Ant.map.associative at this,
                rw function.comp at this,
                simp [this],
            },
            {
                rw ←gdt_ih val,
                rw ←Ant.mark_inactive_leaves,
            },
        },
        case Grd.bang {
            unfold A Ant.map,
            unfold Ant.mark_inactive_leaves Ant.map,
            rw Ant.map.associative,
            rw function.comp,
            unfold Φ.eval,
            --rw ←Ant.mark_inactive_leaves,
            unfold Gdt.mark_inactive_leaves,

            cases is_bottom gdt_grd env,
            case bool.ff {
                simp,
                rw ←gdt_ih env,
                simp [Ant.mark_inactive_leaves],
            },
            case bool.tt {
                simp,
                have := Gdt.mark_inactive_leaves_mark_all_leaves_inactive gdt_tr env,
                rw ←gdt_ih env at this,
                rw ←this,
                simp [Ant.mark_inactive_leaves, Ant.map.associative],
            },
        },
    },
end

lemma redundant_in.monotonous' { a b: Ant bool } (h: a ⟶ b): 
        a.inactive_leaves ⊆ b.inactive_leaves ∧ b.critical_leaf_sets ⊆ a.critical_leaf_sets :=
begin
    induction a generalizing b;
    cases h with h b_a,
    -- case leaf:
    {
        cases a_a; cases b_a;
        finish [Ant.inactive_leaves, Ant.implies.leaf],
    },
    -- case branch:
    {
        specialize a_ih_tr1 h_h1,
        specialize a_ih_tr2 h_h2,
        simp [ *, finset.union_subset_union, Ant.inactive_leaves, Ant.critical_leaf_sets ],
    },
    -- case grd:
    {
        specialize a_ih h_h1,
        split, { simp [Ant.inactive_leaves, a_ih], },

        cases a_a; cases h_b;
        finish [
            Ant.critical_leaf_sets,
            Ant.implies_same_leaves h_h1,
            finset.union_subset_union,
            a_ih.2,
            subset_right_union
        ],
    },
end

lemma redundant_in.monotonous { a b: Ant bool } (leaves: finset Leaf) (h: a ⟶ b):
    leaves.redundant_in a → leaves.redundant_in b :=
begin
    unfold finset.redundant_in,
    have := redundant_in.monotonous' h,
    assume p,
    split,
    {
        rw ←Ant.implies_same_leaves h,
        exact finset.subset.trans p.1 this.1,
    },
    assume e,
    assume q,
    exact p.right e (this.2 q),
end

lemma disjoint_finset { α: Type } [decidable_eq α] { a b: list α } (d : disjoint a.to_finset b.to_finset) : a.disjoint b :=
begin
    unfold list.disjoint,
    assume x h₁ h₂,
    finish [finset.disjoint_iff_ne],
end

theorem card_insert_iff_not_mem { α: Type } [decidable_eq α] {a : α} {s : finset α}: (insert a s).card = s.card + 1 ↔ a ∉ s :=
begin
    split,
    {
        assume h,
        by_contra,
        finish [finset.card_insert_of_mem, s.card.succ_ne_self.symm],
    },
    { exact finset.card_insert_of_not_mem, },
end

theorem nodup_iff_card { α: Type } [decidable_eq α] (a: list α): a.nodup ↔ a.length = a.to_finset.card :=
begin
    split; assume h,
    { simp [list.to_finset_card_of_nodup h], },

    induction a with a as,
    case list.nil { simp, },
    case list.cons {
        rw list.nodup_cons,
        replace h : as.length + 1 = (insert a as.to_finset).card := begin
            simp at h,
            exact h,
        end,
        by_cases a ∈ as.to_finset, {
            replace h : as.length + 1 = as.to_finset.card, { simp [*], },
            have y := list.to_finset_card_le as,
            rw ←h at y,
            simp at y,
            contradiction,
        }, {
            replace x : as.length = as.to_finset.card, { finish, },
            finish,
        }
    },
end 

example {α} [decidable_eq α] (as bs cs ds : list α) : (as ++ bs ++ cs ++ ds).nodup ↔ (ds ++ bs ++ cs ++ as).nodup :=
begin
  rw nodup_iff_card,
  rw nodup_iff_card,
  simp [finset.union_comm, finset.union_left_comm, nat.add_comm, nat.add_left_comm],
end

lemma R_red_partition' { ant: Ant bool } (ant_disjoint: ant.disjoint_leaves):
    ((R ant).acc ++ (R ant).inacc ++ (R ant).red).to_finset = ant.leaves ∧ 
    ((R ant).acc ++ (R ant).inacc ++ (R ant).red).length = ant.leaves.card :=
begin
    induction ant,
    case Ant.leaf {
        unfold R,
        cases ant_a;
        simp [Ant.leaves, R],
    },
    case Ant.branch {
        unfold Ant.disjoint_leaves at ant_disjoint,
        specialize ant_ih_tr1 ant_disjoint.1,
        specialize ant_ih_tr2 ant_disjoint.2.1,
        
        unfold R,
        dsimp only,
        unfold Ant.leaves,
        split, {
            simp [←ant_ih_tr1.1, ←ant_ih_tr2.1, finset.union_comm, finset.union_assoc, finset.union_left_comm],
        },

        rw finset.card_disjoint_union ant_disjoint.2.2,
        simp [←ant_ih_tr1.2, ←ant_ih_tr2.2, nat.add_comm, nat.add_assoc, nat.add_left_comm],
    },
    case Ant.diverge {
        unfold Ant.disjoint_leaves at ant_disjoint,
        specialize ant_ih ant_disjoint,
        cases R_diverge_cases ant_tr ant_a, {
            rw h_R,
            unfold LeafPartition.acc LeafPartition.inacc LeafPartition.red Ant.leaves,
            rw h_R_ant at ant_ih,
            unfold LeafPartition.acc LeafPartition.inacc LeafPartition.red Ant.leaves at ant_ih,
            simp at ant_ih,
            simp [*],
        }, {
            rw h_R,
            exact ant_ih,
        },
    }
end

lemma R_red_partition { ant: Ant bool } (ant_disjoint: ant.disjoint_leaves):
    ((R ant).acc ++ (R ant).inacc ++ (R ant).red).to_finset = ant.leaves ∧ 
    ((R ant).acc ++ (R ant).inacc ++ (R ant).red).nodup :=
begin
    rw nodup_iff_card,
    rw (R_red_partition' ant_disjoint).1,
    rw (R_red_partition' ant_disjoint).2,
    simp,
end    


/-
lemma R_red_partition2 { ant: Ant bool } (ant_disjoint: ant.disjoint_leaves):
    ((R ant).acc ++ (R ant).inacc ++ (R ant).red).to_finset = ant.leaves ∧ 
    ((R ant).acc ++ (R ant).inacc ++ (R ant).red).nodup :=
begin
    induction ant,
    case Ant.leaf {
        unfold R,
        cases ant_a;
        simp [Ant.leaves, R],
    },
    case Ant.branch {
        unfold Ant.disjoint_leaves at ant_disjoint,
        specialize ant_ih_tr1 ant_disjoint.1,
        specialize ant_ih_tr2 ant_disjoint.2.1,
        
        unfold R,
        unfold LeafPartition.acc LeafPartition.inacc LeafPartition.red Ant.leaves,
        split, { finish, },

        suffices : (((R ant_tr1).acc ++ (R ant_tr1).inacc ++ (R ant_tr1).red)
            ++ ((R ant_tr2).acc ++ (R ant_tr2).inacc ++ (R ant_tr2).red)).nodup, {
            rw list.nodup_append_comm
            
        },

        apply list.nodup_append.2,
        split, { exact ant_ih_tr1.2, },
        split, { exact ant_ih_tr2.2, },

        have d := ant_disjoint.2.2,
        rw ←ant_ih_tr1.1 at d,
        rw ←ant_ih_tr2.1 at d,
        
        apply disjoint_finset d,
    },
    case Ant.diverge {
        sorry,
    }
end
-/

lemma R_red_l_not_mem_ls { ant: Ant bool } (ant_disjoint: ant.disjoint_leaves) { l: Leaf } { ls: list Leaf } (h: (R ant).red = l::ls):
    l ∉ ls.to_finset :=
begin
    have : (R ant).red.nodup := begin
        exact list.nodup_of_nodup_append_right (R_red_partition ant_disjoint).2,
    end,
    rw h at this,
    simp [list.not_mem_of_nodup_cons this],
end

lemma R_acc_l_not_mem { ant: Ant bool } (ant_disjoint: ant.disjoint_leaves) { l: Leaf } { ls: list Leaf } (h: (R ant).acc = l::ls):
    l ∉ (R ant).red.to_finset :=
begin
    have d := list.disjoint_of_nodup_append (R_red_partition ant_disjoint).2,
    have : l ∈ ((R ant).acc ++ (R ant).inacc) := by simp [h],
    suffices : l ∉ (R ant).red, { simp [this], },
    exact imp_false.mp (@d l this),
end

lemma R_inacc_l_not_mem { ant: Ant bool } (ant_disjoint: ant.disjoint_leaves) { l: Leaf } { ls: list Leaf } (h: (R ant).inacc = l::ls):
    l ∉ (R ant).red.to_finset :=
begin
    have d := list.disjoint_of_nodup_append (R_red_partition ant_disjoint).2,
    have : l ∈ ((R ant).acc ++ (R ant).inacc) := by simp [h],
    suffices : l ∉ (R ant).red, { simp [this], },
    exact imp_false.mp (@d l this),
end

lemma R_acc_subset_leaves { ant: Ant bool } (ant_disjoint: ant.disjoint_leaves): (R ant).acc.to_finset ⊆ ant.leaves :=
begin
    have := (R_red_partition ant_disjoint).1,
    replace this := finset.subset_of_eq this,
    rw finset.subset_iff at this,
    simp at this,
    rw finset.subset_iff,
    finish,
end

lemma R_inacc_subset_leaves { ant: Ant bool } (ant_disjoint: ant.disjoint_leaves): (R ant).inacc.to_finset ⊆ ant.leaves :=
begin
    have := (R_red_partition ant_disjoint).1,
    replace this := finset.subset_of_eq this,
    rw finset.subset_iff at this,
    simp at this,
    rw finset.subset_iff,
    finish,
end

lemma R_red_subset_leaves { ant: Ant bool }: (R ant).red.to_finset ⊆ ant.leaves :=
begin
    induction ant,
    case Ant.leaf {
        cases ant_a;
        simp [R, Ant.leaves],
    },
    case Ant.branch {
        simp [R, Ant.leaves, finset.union_subset_union, *],
    },
    case Ant.diverge {
        cases R_diverge_cases ant_tr ant_a, {
            rw h_R,
            rw h_R_ant at ant_ih,
            unfold LeafPartition.red at ant_ih,
            rw list.to_finset_cons at ant_ih,
            simp [Ant.leaves, finset.insert_subset.1 ant_ih],
        }, {
            simp [*, Ant.leaves],
        },
    },
end

lemma critical_leaf_set_elements { ant: Ant bool } { e: finset Leaf } (h: e ∈ ant.critical_leaf_sets):
    e ⊆ ant.leaves :=
begin
    induction ant;
    rw Ant.critical_leaf_sets at h,
    case Ant.leaf {
        finish,
    },
    case Ant.branch {
        simp at h,
        cases h;
        simp [Ant.leaves, subset_right_union, subset_left_union, *],
    },
    case Ant.diverge {
        simp at h,
        cases h;
        try {
            cases ant_a;
            finish [Ant.leaves],
        },
    },
end

lemma subset_inter_subset { α: Type } [decidable_eq α] { s1 s2 s3: finset α }: s1 ⊆ s3 → s1 ∩ s2 ⊆ s3 :=
begin
    refine finset.subset.trans _,
    exact finset.inter_subset_left s1 s2,
end

lemma subset_inter_subset_subset { α: Type } [decidable_eq α] { s1 s2 s3: finset α } (h: s1 ⊆ s2): s1 ∩ s2 ⊆ s3 ↔ s1 ⊆ s3 :=
begin
    split, {
        refine finset.subset.trans _,
        refine finset.subset_inter _ h,
        exact finset.subset.refl s1,
    }, {
        exact subset_inter_subset,
    },
end

lemma not_subset { α: Type } { u v: finset α }: ¬ u ⊆ v ↔ ∃ x ∈ u, ¬ x ∈ v :=
begin
    exact not_ball
end

lemma Ant.leaves_non_empty { α: Type } (ant: Ant α) : ∃ l, l ∈ ant.leaves :=
begin
    induction ant,
    case Ant.leaf { simp [Ant.leaves], },
    case Ant.diverge { simp [Ant.leaves, *], },
    case Ant.branch {
        cases ant_ih_tr1 with leaf,
        use leaf,
        simp [Ant.leaves, *],
    }
end

@[simp]
lemma Ant.disjoint_leaves_of_map { α β: Type } { f: α → β } { ant: Ant α }: (ant.map f).disjoint_leaves ↔ ant.disjoint_leaves :=
by induction ant; { simp [Ant.map, Ant.disjoint_leaves, *], }

lemma Ant.disjoint_leaves_of_mark_inactive_leaves_eq { ant1 ant2: Ant Φ } { env: Env } (h: ant1.mark_inactive_leaves env = ant2.mark_inactive_leaves env):
    ant1.disjoint_leaves ↔ ant2.disjoint_leaves :=
begin
    unfold Ant.mark_inactive_leaves at h,
    have : (Ant.map (λ (ty : Φ), !ty.eval env) ant1).disjoint_leaves ↔ (Ant.map (λ (ty : Φ), !ty.eval env) ant2).disjoint_leaves :=
    begin
        simp [h],
    end,
    simp at this,
    exact this,
end

lemma Ant.disjoint_leaves_of_gdt_disjoint_leaves { gdt: Gdt } (h: gdt.disjoint_leaves): (A gdt).disjoint_leaves :=
begin
    induction gdt,
    case Gdt.leaf { simp [A], },
    case Gdt.branch {
        unfold Gdt.disjoint_leaves at h,
        simp [A, Gdt.disjoint_leaves, Ant.disjoint_leaves, *],
    },
    case Gdt.grd {
        unfold Gdt.disjoint_leaves at h,
        cases gdt_grd;
        { simp [A, Ant.disjoint_leaves, *], },
    },
end

lemma R_red_redundant { ant: Ant bool }
    (ant_disjoint: ant.disjoint_leaves)
    : (R ant).red.to_finset.redundant_in ant :=
begin
    induction ant,

    case Ant.leaf {
        unfold finset.redundant_in R,
        cases ant_a;
        simp [Ant.critical_leaf_sets, Ant.inactive_leaves, Ant.leaves],
    },
    case Ant.branch {
        unfold Ant.disjoint_leaves at ant_disjoint,
        specialize ant_ih_tr1 ant_disjoint.1,
        specialize ant_ih_tr2 ant_disjoint.2.1,

        unfold finset.redundant_in R,
        unfold finset.redundant_in R at ant_ih_tr1,
        unfold finset.redundant_in R at ant_ih_tr2,
        unfold LeafPartition.red,
        split, {
            simp [Ant.inactive_leaves, finset.union_subset_union ant_ih_tr1.1 ant_ih_tr2.1, Ant.leaves],
            replace ant_ih_tr1 := ant_ih_tr1.1,
            replace ant_ih_tr2 := ant_ih_tr2.1,
            rw subset_inter_subset_subset R_red_subset_leaves at ant_ih_tr1,
            rw subset_inter_subset_subset R_red_subset_leaves at ant_ih_tr2,
            apply subset_inter_subset,
            exact finset.union_subset_union ant_ih_tr1 ant_ih_tr2,
        },

        assume e,
        assume h,
        rw Ant.critical_leaf_sets at h,
        
        simp [Ant.leaves],
        replace ant_ih_tr1 := ant_ih_tr1.2,
        replace ant_ih_tr2 := ant_ih_tr2.2,
        simp at h,
        cases h, {
            specialize ant_ih_tr1 e h,
            rw not_subset,
            rw not_subset at ant_ih_tr1,
            cases ant_ih_tr1 with x ant_ih_tr1,
            cases ant_ih_tr1 with H ant_ih_tr1,
            
            have : x ∉ (R ant_tr2).red.to_finset :=
            begin
                by_contradiction,
                have h1 := finset.subset_iff.1 (critical_leaf_set_elements h) H,
                have h2 := finset.subset_iff.1 (R_red_subset_leaves) a,
                have := finset.disjoint_iff_ne.1 ant_disjoint.2.2 _ h1 _ h2,
                simp at this,
                exact this,
            end,
            use x,
            simp [*],
        },  
        {
            specialize ant_ih_tr2 e h,
            rw not_subset,
            rw not_subset at ant_ih_tr2,
            cases ant_ih_tr2 with x ant_ih_tr2,
            cases ant_ih_tr2 with H ant_ih_tr2,
            
            have : x ∉ (R ant_tr1).red.to_finset :=
            begin
                by_contradiction,
                have h1 := finset.subset_iff.1 (critical_leaf_set_elements h) H,
                have h2 := finset.subset_iff.1 (R_red_subset_leaves) a,
                have := finset.disjoint_iff_ne.1 ant_disjoint.2.2 _ h2 _ h1,
                simp at this,
                exact this,
            end,
            use x,
            simp [*],
        }
    },
    case Ant.diverge {
        unfold finset.redundant_in,
        unfold finset.redundant_in at ant_ih,
        unfold Ant.disjoint_leaves at ant_disjoint,
        specialize ant_ih ant_disjoint,
        split, {
            cases R_diverge ant_a (refl (R ant_tr)) with d d,
            case or.inl {
                cases d with leaf d,
                cases d with ls d,
                rw d.2.2,
                unfold LeafPartition.red,
                rw d.2.1 at ant_ih,
                unfold LeafPartition.red at ant_ih,
                unfold Ant.inactive_leaves,
                unfold Ant.leaves,
                have : ls.to_finset ⊆ (leaf :: ls).to_finset := by simp [finset.subset_insert],
                have := finset.inter_subset_inter this (finset.subset.refl _),
                exact finset.subset.trans this ant_ih.1,
            },
            case or.inr {
                simp [d.2, Ant.inactive_leaves, ant_ih.1],
                unfold Ant.leaves,
                exact ant_ih.1,
            },
        },

        assume e,
        assume h,


        unfold Ant.critical_leaf_sets at h,

        cases R_diverge ant_a (refl (R ant_tr)) with d d,
        case or.inr {
            cases d,
            rw d_right,
            cases ant_a,
            case bool.tt {
                simp [d_left] at h,
                exact ant_ih.2 e h,
            },
            simp at h,
            cases h, { exact ant_ih.2 e h, },
            rw h,
            cases d_left, {
                finish,
            },
            cases d_left, {
                rw not_subset,
                cases c: (R ant_tr).acc with acc accs, { finish, },
                use acc,
                split, {
                    have x : acc ∈ (R ant_tr).acc.to_finset := by simp [c],
                    have := R_acc_subset_leaves ant_disjoint,
                    rw finset.subset_iff at this,
                    exact @this acc x,
                }, {
                    exact R_acc_l_not_mem ant_disjoint c,
                },
            },
            cases d_left, {
                rw not_subset,
                cases c: (R ant_tr).inacc with inacc inaccs, { finish, },
                use inacc,
                split, {
                    have x : inacc ∈ (R ant_tr).inacc.to_finset := by simp [c],
                    have := R_inacc_subset_leaves ant_disjoint,
                    rw finset.subset_iff at this,
                    exact @this inacc x,
                }, {
                    exact R_inacc_l_not_mem ant_disjoint c,
                },
            },
            {
                rw not_subset,
                have := Ant.leaves_non_empty ant_tr,
                cases this with l ls,
                rw d_left,
                use l,
                split, { exact ls, },
                simp,
            }
        },

        case or.inl {
            cases d with leaf d,
            cases d with ls d,
            rw d.1 at h,
            simp at h,
            rw d.2.2,
            unfold LeafPartition.red,
            rw d.2.1 at ant_ih,
            unfold LeafPartition.red at ant_ih,
            rw not_subset,
            have := ant_ih.2 e,
            rw not_subset at this,
            cases h, {
                specialize this h,
                cases this with x this,
                cases this with H this,
                use x,
                simp at this,
                finish,
            }, {
                use leaf,
                rw h,
                have : leaf ∈ (R ant_tr).red.to_finset := by simp [*],
                have := finset.subset_iff.1 R_red_subset_leaves this,
                split, { exact this, },
                apply R_red_l_not_mem_ls ant_disjoint,
                rw d.2.1,
            }
        },
    },
end

theorem R_red_removable
    (can_prove_empty: Gs)
    (gdt: Gdt) (gdt_disjoint: gdt.disjoint_leaves)
    (Agdt: Ant Φ)
    (ant_def: Agdt.mark_inactive_leaves = (A gdt).mark_inactive_leaves):
    Gdt.eval_option (gdt.remove_leaves ((R $ Agdt.map can_prove_empty.val).red.to_finset)) = gdt.eval :=
begin
    ext env:1,
    
    -- `Agdt` semantically equals `A gdt`, which represents `gdt` by annotating it with refinement types.
    -- `Agdt` and `A gdt` don't need to be syntactically equal though!
    -- In fact, `𝒜 gdt` and `A gdt` are semantically equal, but not syntactically.

    -- `can_prove_empty` approximates emptiness for a single refinement type.
    -- `ant_empt` approximates emptiness of the refinement types in `Agdt` for every `env`.
    -- It also approximates inactive leaves of `gdt` in context of `env` (ant_empt_imp_gdt).
    let ant_empt := Agdt.map can_prove_empty.val,
    have ant_empt_imp_gdt := calc
        ant_empt ⟶ Agdt.mark_inactive_leaves env : can_prove_empty_implies_inactive can_prove_empty Agdt env
        ...      ⟶ (A gdt).mark_inactive_leaves env : by simp [Ant.implies.refl, ant_def]
        ...      ⟶ gdt.mark_inactive_leaves env : by simp [Ant.implies.refl, A_mark_inactive_leaves gdt env],

    -- Since `gdt` has disjoint leaves, `ant_empt` has disjoint leaves too.
    have ant_empt_disjoint : ant_empt.disjoint_leaves
        := by simp [Ant.disjoint_leaves_of_gdt_disjoint_leaves gdt_disjoint,
                Ant.disjoint_leaves_of_mark_inactive_leaves_eq (function.funext_iff.1 ant_def env)],

    -- The set of leaves `R_red` is redundant in `ant_empt` (red_in_ant_empt).
    -- This means that these leaves are inactive
    -- and not all leaves of possibly active diverge nodes are redundant.
    let R_red := (R ant_empt).red.to_finset,
    have red_in_ant_empt: R_red.redundant_in ant_empt := R_red_redundant ant_empt_disjoint,
    
    -- Since `redundant_in` is monotonous and `ant_empt` approximates inactive leaves on `gdt`,
    -- `R_red` is also redundant in `gdt` (red_in_gdt).
    have red_in_gdt: R_red.redundant_in (gdt.mark_inactive_leaves env)
        := redundant_in.monotonous _ ant_empt_imp_gdt red_in_ant_empt,
    
    -- Since `R_red` is a redundant set, it can be removed from `gdt` without
    -- changing the semantics. Note that `R_red` is independent of env.
    have this: Gdt.eval_option (Gdt.remove_leaves R_red gdt) env = gdt.eval env
        := redundant_leaves_removable gdt gdt_disjoint env _ red_in_gdt,

    -- This finishes the proof.
    exact this,
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
        cases (R_diverge_cases ant_tr ant_a);
        rw h_R,
        case R_diverge_case.case1 {
            simp [h_R_ant, finset.insert_eq] at ant_ih,
            simp [R, Ant.inactive_leaves, ant_ih],
        },
        case R_diverge_case.case2 {
            simp [Ant.inactive_leaves, ant_ih],
        },
    }
end

lemma disjoint_sets { α: Type } [decidable_eq α] { a₁ a₂ b₁ b₂: finset α } (h: disjoint b₁ b₂) (h₁: a₁ ⊆ b₁) (h₂: a₂ ⊆ b₂):
    (b₁ ∪ b₂) \ (a₁ ∪ a₂) = (b₁ \ a₁) ∪ (b₂ \ a₂) :=
begin
    rw finset.subset_iff at h₁,
    rw finset.subset_iff at h₂,
    rw finset.ext_iff,
    assume a,
    specialize @h₁ a,
    specialize @h₂ a,
    rw finset.disjoint_iff_inter_eq_empty at h,
    rw finset.ext_iff at h,
    specialize @h a,
    
    finish,
end

lemma gdt_mark_inactive_leaves_inactive_leaves_of_diverged_or_no_match { gdt: Gdt } { env: Env }:
    (gdt.mark_inactive_leaves env).inactive_leaves = gdt.leaves ↔ gdt.eval env = Result.diverged ∨ gdt.eval env = Result.no_match :=
begin
    induction gdt with leaf generalizing env,
    case Gdt.leaf {
        simp [Gdt.eval, Gdt.mark_inactive_leaves, Ant.inactive_leaves, Gdt.leaves, ne.symm (finset.singleton_ne_empty leaf)],
    },
    case Gdt.grd {
        cases gdt_grd,
        case Grd.xgrd {
            cases c: xgrd_eval gdt_grd env,
            { simp [Gdt.leaves, grd_eval_xgrd_none c, Gdt.mark_inactive_leaves, c], },
            { simp [Gdt.leaves, grd_eval_xgrd_some c, Gdt.mark_inactive_leaves, *], },
        },
        case Grd.bang {
            cases c: is_bottom gdt_grd env,
            { simp [Gdt.leaves, grd_eval_bang_not_bottom c, Gdt.mark_inactive_leaves, Ant.inactive_leaves, *], },
            { simp [Gdt.leaves, grd_eval_bang_bottom c, Gdt.mark_inactive_leaves, Ant.inactive_leaves, c], },
        }
    },
    case Gdt.branch {
        simp [Gdt.mark_inactive_leaves, Ant.inactive_leaves],
        by_cases c: gdt_tr1.eval env = Result.no_match;
        simp [c, Gdt.leaves],
        {
            rw ←gdt_ih_tr2,
            rw Gdt.mark_inactive_leaves_no_match c,
            rw Gdt.mark_all_leaves_inactive.inactive_leaves,
            sorry,
        }, {
            sorry,
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
            { simp [Gdt.leaves, grd_eval_xgrd_none c, Gdt.mark_inactive_leaves, c, ne.symm (finset.singleton_ne_empty _)], },
            { simp [Gdt.leaves, grd_eval_xgrd_some c, Gdt.mark_inactive_leaves, @gdt_ih gdt_disjoint val, *], },
        },
        case Grd.bang {
            cases c: is_bottom gdt_grd env,
            { simp [Gdt.leaves, grd_eval_bang_not_bottom c, Gdt.mark_inactive_leaves, Ant.inactive_leaves, *], },
            { simp [Gdt.leaves, grd_eval_bang_bottom c, Gdt.mark_inactive_leaves, Ant.inactive_leaves, c, @gdt_ih gdt_disjoint env, ne.symm (finset.singleton_ne_empty _)], },
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
        rw Gdt.eval_branch_match_2,
        rw ←gdt_ih_tr2,
        rw ←gdt_ih_tr1,
        
        cases c: (gdt_tr1.eval env).is_match, {
            simp at c,
            simp [c, gdt_mark_inactive_leaves_inactive_leaves_of_diverged_or_no_match.2 (or.inr c), ne.symm (finset.singleton_ne_empty _)],
        }, {
            simp at c,
            simp [c],
        }
    },
end

lemma Gdt.eval.leaf_mem_leaves { gdt: Gdt } { env: Env } { leaf: Leaf } (h: gdt.eval env = Result.leaf leaf): leaf ∈ gdt.leaves :=
begin
    induction gdt with leaf generalizing env,
    case Gdt.leaf {
        finish [Gdt.leaves, Gdt.eval],
    },
    case Gdt.grd {
        cases gdt_grd,
        case Grd.xgrd {
            cases c: xgrd_eval gdt_grd env,
            { finish [Gdt.leaves, grd_eval_xgrd_none c, Gdt.eval], },
            { finish [Gdt.leaves, grd_eval_xgrd_some c, Gdt.eval], },
        },
        case Grd.bang {
            cases c: is_bottom gdt_grd env,
            { finish [Gdt.leaves, grd_eval_bang_not_bottom c], },
            { finish [Gdt.leaves, grd_eval_bang_bottom c], },
        }
    },
    case Gdt.branch {
        by_cases c: gdt_tr1.eval env = Result.no_match;
        finish [Gdt.leaves,  Gdt.eval_branch_match_2],
    },
end

lemma f__oo { gdt: Gdt } { env: Env } { leaf: Leaf } { ant: Ant bool }
    (gdt_disjoint: gdt.disjoint_leaves)
    (can_prove_empty: Gs)
    (ant_def: (A gdt).mark_inactive_leaves env = ant)
    (h: gdt.eval env = Result.leaf leaf):
    leaf ∈ (R ant).acc \ ((R ant).inacc ++ (R ant).red) :=
begin
    rw ←gdt_mark_inactive_leaves_inactive_leaves_of_leaf_match gdt_disjoint at h,
    rw A_mark_inactive_leaves gdt env at ant_def,
    rw ant_def at h,

    have : leaf ∉ ant.inactive_leaves :=
    begin
        rw finset.ext_iff at h,
        specialize h leaf,
        simp at h,
        exact h.2,
    end,

    have x : leaf ∉ (R ant).inacc ++ (R ant).red :=
    begin
        have := r_correct_1 ant,
        rw finset.subset_iff at this,
        specialize @this leaf,
        finish,
    end,
    
    have : leaf ∈ (R ant).acc :=
    begin
        have ant_disjoint: ant.disjoint_leaves := by sorry,
        have := (R_red_partition ant_disjoint).1,
        have l : leaf ∈ ant.leaves := by sorry,
        rw ←this at l,
        simp at x,
        push_neg at x,
        simp [x] at l,
        exact l,
    end,

end
