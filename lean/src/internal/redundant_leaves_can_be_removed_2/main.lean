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

lemma can_prove_empty_implies_inactive { can_prove_empty: Gs } { ant: Ant Φ } { env: Env }:
    (ant.map (can_prove_empty.val)) ⇒ (ant.mark_inactive_leaves env) :=
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
            have : gdt_tr1.eval env = Result.no_match, { cases gdt_tr1.eval env; finish, },
            specialize gdt_ih_tr1 env,
            unfold Ant.mark_inactive_leaves at gdt_ih_tr1,
            specialize gdt_ih_tr2 env,
            unfold Ant.mark_inactive_leaves at gdt_ih_tr2,
            
            simp [c, ←Gdt.mark_inactive_leaves_no_match this, *],
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
            sorry,
        },
    },
end

lemma removable.monotonous' { a b: Ant bool } (h: a ⇒ b): 
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

lemma removable.monotonous { a b: Ant bool } (leaves: finset Leaf) (h: a ⇒ b):
    leaves.removable_in a → leaves.removable_in b :=
begin
    unfold finset.removable_in,
    have := removable.monotonous' h,
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

lemma R_red_removable (ant: Ant bool)
    --(ant_disjoint: ant.disjoint_leaves)
    : (R ant).red.to_finset.removable_in ant :=
begin
    induction ant,

    case Ant.leaf {
        unfold finset.removable_in R,
        cases ant_a;
        simp [Ant.critical_leaf_sets, Ant.inactive_leaves, Ant.leaves],
    },
    case Ant.branch {
        unfold finset.removable_in R,
        unfold finset.removable_in R at ant_ih_tr1,
        unfold finset.removable_in R at ant_ih_tr2,
        unfold LeafPartition.red,
        split, {
            simp [Ant.inactive_leaves, finset.union_subset_union ant_ih_tr1.1 ant_ih_tr2.1, Ant.leaves],
            sorry,
        },

        assume e,
        assume h,
        rw Ant.critical_leaf_sets at h,
        
        simp,
        sorry,
    },
    case Ant.diverge {
        unfold finset.removable_in,
        unfold finset.removable_in at ant_ih,

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
                sorry,
            },
            case or.inr {
                simp [d.2, Ant.inactive_leaves, ant_ih.1],
                sorry,
            },
        },

        assume e,
        assume h,


        unfold Ant.critical_leaf_sets at h,

        cases R_diverge ant_a (refl (R ant_tr)) with d d,
        case or.inr {
            rw d.2,
            sorry,
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
            sorry,
        },
    },
end

theorem redundant_leaves_removable
    (can_prove_empty: Gs)
    (gdt: Gdt) (gdt_disjoint: gdt.disjoint_leaves):
    Gdt.eval_option (gdt.remove_leaves ((R $ (A gdt).map can_prove_empty.val).red.to_finset)) = gdt.eval :=
begin
    ext env:1,
    
    -- `A gdt` represents `gdt` by annotating it with refinement types.
    -- `can_prove_empty` approximates emptiness for a single refinement type.
    let ant := (A gdt).map can_prove_empty.val,

    -- `ant` approximates emptiness of these refinement types for every `env` (s1).
    have s1: ant ⇒ (A gdt).mark_inactive_leaves env
        := @can_prove_empty_implies_inactive _ can_prove_empty (A gdt) env,

    -- Since a refinement type in `A gdt` is empty in `env` iff
    -- the corresponding leaf- or diverge-node in `gdt` is inactive in `env` (s2),
    have s2: (A gdt).mark_inactive_leaves env = gdt.mark_inactive_leaves env
        := A_mark_inactive_leaves gdt env,
    -- `ant` also approximates inactive leaves of `gdt` in context of `env` (s3).
    have s3: ant ⇒ gdt.mark_inactive_leaves env
        := eq.subst s2 s1,

    -- `R_red_leaves` is the set we want to remove.
    let R_red_leaves := (R ant).red.to_finset,

    -- The set of leaves `R_red_leaves` is removable in `ant`.
    -- This means that these leaves are inactive
    -- and possibly active diverge nodes are not removed.
    have s4: R_red_leaves.removable_in ant 
        := R_red_removable ant,
    
    -- Since `removable` is monotonous and `ant` approximates inactive leaves on `gdt`,
    -- `R_red_leaves` can also be removed from `gdt` (s5).
    have s5: R_red_leaves.removable_in (gdt.mark_inactive_leaves env)
        := removable.monotonous _ s3 s4,
    
    -- Since `R_red_leaves` is a removable set, it can be removed from `gdt` without
    -- changing the semantics. Note that `R_red_leaves` is independent of env.
    have s6: Gdt.eval_option (Gdt.remove_leaves R_red_leaves gdt) env = gdt.eval env
        := removable_leaves_can_be_removed gdt gdt_disjoint env _ s5,

    -- This finishes the proof.
    exact s6,
end
