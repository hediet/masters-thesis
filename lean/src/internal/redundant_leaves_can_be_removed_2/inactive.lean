import tactic
import ...definitions
import ..helper_defs
import data.finset
import ..utils
import data.list
import data.bool
import ..leaves_theory
import ..gdt_eval
import ..gdt_eval_option

open finset

variable [GuardModule]
open GuardModule

def Gdt.mark_all_leaves_inactive: Gdt → Ant bool
| (Gdt.leaf leaf) := Ant.leaf tt leaf 
| (Gdt.branch tr1 tr2) := Ant.branch tr1.mark_all_leaves_inactive tr2.mark_all_leaves_inactive
| (Gdt.grd (Grd.xgrd _) tr) := tr.mark_all_leaves_inactive
| (Gdt.grd (Grd.bang _) tr) := Ant.diverge tt tr.mark_all_leaves_inactive

@[simp]
lemma Gdt.mark_all_leaves_inactive.inactive_leaves (gdt: Gdt):
    gdt.mark_all_leaves_inactive.inactive_leaves = gdt.leaves :=
begin
    induction gdt;
    try { cases gdt_grd };
    simp [*, Gdt.leaves, Gdt.mark_all_leaves_inactive, Ant.inactive_leaves],
end

@[simp]
lemma Gdt.mark_all_leaves_inactive.critical_leaf_sets (gdt: Gdt):
    gdt.mark_all_leaves_inactive.critical_leaf_sets = ∅ :=
begin
    induction gdt;
    try { cases gdt_grd };
    simp [*, Gdt.leaves, Gdt.mark_all_leaves_inactive, Ant.critical_leaf_sets],
end

@[simp]
lemma Gdt.mark_all_leaves_inactive.leaves (gdt: Gdt):
    gdt.mark_all_leaves_inactive.leaves = gdt.leaves :=
begin
    induction gdt;
    try { cases gdt_grd };
    simp [*, Gdt.leaves, Gdt.mark_all_leaves_inactive, Ant.critical_leaf_sets, Ant.leaves],
end

@[simp]
lemma Gdt.mark_all_leaves_inactive_map_false (gdt: Gdt):
    gdt.mark_all_leaves_inactive.map (λ x, tt) = gdt.mark_all_leaves_inactive :=
begin
    induction gdt;
    try { cases gdt_grd };
    simp [*, Ant.map, Gdt.mark_all_leaves_inactive],
end

def Gdt.mark_inactive_leaves : Gdt → Env → Ant bool
| (Gdt.leaf leaf) env := Ant.leaf ff leaf 
| (Gdt.branch tr1 tr2) env :=
    Ant.branch (tr1.mark_inactive_leaves env) (
        if (tr1.eval env).is_match then
            (tr2.mark_all_leaves_inactive)
        else
            (tr2.mark_inactive_leaves env)
    )
| (Gdt.grd (Grd.xgrd grd) tr) env :=
    match xgrd_eval grd env with
    | none := tr.mark_all_leaves_inactive
    | some env' := tr.mark_inactive_leaves env'
    end
| (Gdt.grd (Grd.bang var) tr) env :=
    if is_bottom var env
    then Ant.diverge ff (tr.mark_all_leaves_inactive)
    else Ant.diverge tt (tr.mark_inactive_leaves env)

lemma Gdt.mark_inactive_leaves_mark_all_leaves_inactive (gdt: Gdt) (env: Env):
    (gdt.mark_inactive_leaves env).map (λ x, tt) = gdt.mark_all_leaves_inactive :=
begin
    induction gdt generalizing env;
    try { cases gdt_grd };
    try { cases c: (gdt_tr1.eval env).is_match };
    try { cases c: (xgrd_eval gdt_grd env) };
    try { cases c: is_bottom gdt_grd env };
    simp [*, Gdt.leaves, Gdt.mark_inactive_leaves, Gdt.mark_all_leaves_inactive, Ant.leaves, Ant.map],
end

@[simp]
lemma Gdt.mark_inactive_leaves.leaves (gdt: Gdt) (env: Env):
    (gdt.mark_inactive_leaves env).leaves = gdt.leaves :=
begin
    induction gdt generalizing env;
    try { cases gdt_grd };
    try { cases c: (gdt_tr1.eval env).is_match };
    try { cases c: (xgrd_eval gdt_grd env) };
    try { cases c: is_bottom gdt_grd env };
    simp [*, Gdt.leaves, Gdt.mark_inactive_leaves, Ant.critical_leaf_sets, Ant.leaves],
end

lemma Gdt.mark_inactive_leaves.inactive_leaves (gdt: Gdt) (env: Env): (gdt.mark_inactive_leaves env).inactive_leaves ⊆ gdt.leaves :=
by simp only [←Gdt.mark_inactive_leaves.leaves gdt env, Ant.inactive_leaves_subset_leaves]

lemma Gdt.mark_inactive_leaves_no_match { env: Env } { gdt: Gdt } (h: gdt.eval env = Result.no_match):
    gdt.mark_inactive_leaves env = gdt.mark_all_leaves_inactive :=
begin
    induction gdt with leaf generalizing env,
    case Gdt.leaf {
        finish [Gdt.eval],
    },
    case Gdt.branch {
        simp [
            Gdt.mark_inactive_leaves, Gdt.mark_all_leaves_inactive,
            gdt_eval_branch_no_match.1 h, *
        ],
    },
    case Gdt.grd {
        cases gdt_grd with gdt_grd var,
        case Grd.xgrd {
            cases c: xgrd_eval gdt_grd env, {
                simp [Gdt.mark_inactive_leaves, Gdt.mark_all_leaves_inactive, c],
            }, {
                rw [grd_eval_xgrd_some c] at h,
                simp [Gdt.mark_inactive_leaves, Gdt.mark_all_leaves_inactive, c, gdt_ih h],
            },
        },
        case Grd.bang {
            simp [Gdt.mark_inactive_leaves, Gdt.mark_all_leaves_inactive, grd_eval_bang_no_match.1 h, gdt_ih],
        }
    }
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

lemma redundant_in_mark_all_leaves_inactive (gdt: Gdt) (leaves: finset Leaf): leaves.redundant_in gdt.mark_all_leaves_inactive :=
begin
    unfold redundant_in,
    simp [inter_subset_right],
end

lemma sets_3 { α: Type } [decidable_eq α] { a b c : finset α }
  (h : ¬ a ∪ b ⊆ c):
  ¬a ⊆ c ∨ ¬b ⊆ c :=
begin
    by_contra x,
    push_neg at x,
    have : a ∪ b ⊆ c :=
    begin
        rw finset.subset_iff,
        simp,
        rw finset.subset_iff at x,
        rw finset.subset_iff at x,
        tauto,
    end,
    contradiction,
end

lemma remove_leaves_branch { leaves: finset Leaf } { gdt₁ gdt₂: Gdt }:
    (gdt₁.branch gdt₂).remove_leaves leaves ≠ none ↔
         gdt₁.remove_leaves leaves ≠ none ∨
         gdt₂.remove_leaves leaves ≠ none :=
begin
    unfold Gdt.remove_leaves,
    cases gdt₁.remove_leaves leaves;
    cases gdt₂.remove_leaves leaves;
    simp [Gdt.branch_option],
end

lemma Gdt.grd_option_neq_none { gdt: option Gdt } { grd: Grd }: Gdt.grd_option grd gdt ≠ none ↔ gdt ≠ none :=
begin
    cases gdt;
    simp [Gdt.grd_option],
end

lemma remove_leaves_neq_none { leaves: finset Leaf } { gdt: Gdt } (h: ¬ gdt.leaves ⊆ leaves): (Gdt.remove_leaves leaves gdt) ≠ none :=
begin
    induction gdt with leaf,
    case Gdt.leaf {
        simp only [Gdt.leaves, singleton_subset_iff] at h,
        simp [Gdt.remove_leaves, h],
    },
    case Gdt.branch {
        simp only [Gdt.leaves] at h,
        rw remove_leaves_branch,
        have := sets_3 h,
        cases this;
        simp [*],
    },
    case Gdt.grd {
        unfold Gdt.remove_leaves,
        unfold Gdt.leaves at h,
        rw Gdt.grd_option_neq_none,
        simp [gdt_ih h],
    }
end

lemma redundant_leaves_removable
    (gdt: Gdt) (gdt_disjoint: gdt.disjoint_leaves)
    -- We only focus on a very particular environment `env`.
    (env: Env)
    (leaves: finset Leaf) (leaves_def: leaves.redundant_in (gdt.mark_inactive_leaves env)):

        Gdt.eval_option (gdt.remove_leaves leaves) env = gdt.eval env :=
begin
  induction gdt with leaf generalizing env,
  case Gdt.leaf {
      simp [Gdt.eval],
      unfold Gdt.mark_inactive_leaves finset.redundant_in at leaves_def,
      simp [Ant.inactive_leaves, Ant.critical_leaf_sets, Ant.leaves] at leaves_def,
      unfold Gdt.remove_leaves,
      have : ¬leaf ∈ leaves := disjoint_singleton.mp leaves_def,
      simp [this, Gdt.eval_option],
  },

  case Gdt.branch {
        simp [Gdt.mark_inactive_leaves, -Result.is_match_neq_no_match] at leaves_def,
        unfold Gdt.remove_leaves,
        unfold Gdt.disjoint_leaves at gdt_disjoint,

        cases c: (gdt_tr1.eval env).is_match,
        
        case bool.ff {
            rw c at leaves_def,
            simp at c,
            simp [Ant.inactive_leaves, Gdt.mark_inactive_leaves, finset.redundant_in, Ant.critical_leaf_sets ] at leaves_def,
            simp [Ant.leaves, Gdt.mark_inactive_leaves_no_match c] at leaves_def,

            have : leaves.redundant_in (gdt_tr1.mark_inactive_leaves env) :=
            by simp [Gdt.mark_inactive_leaves_no_match c, redundant_in_mark_all_leaves_inactive],

            specialize gdt_ih_tr1 gdt_disjoint.1 env this,

            have : leaves.redundant_in (gdt_tr2.mark_inactive_leaves env) :=
            begin
                have := sets_1 leaves_def.1 gdt_disjoint.2.2,
                unfold redundant_in,
                split, { simp [*], },
                exact leaves_def.2,
            end,

            specialize gdt_ih_tr2 gdt_disjoint.2.1 env this,
            rw ←Gdt.eval_option at gdt_ih_tr2,
            rw Gdt.branch_option_replace_right_env _ (or.intro_left _ gdt_ih_tr2),
            rw ←Gdt.eval_option at gdt_ih_tr1,
            rw Gdt.branch_option_replace_left_env gdt_ih_tr1,
            simp,
        },
        case bool.tt {
            rw c at leaves_def,
            simp at c,
            simp [Ant.inactive_leaves, Gdt.mark_inactive_leaves, redundant_in, Ant.critical_leaf_sets ] at leaves_def,
            simp [Ant.leaves] at leaves_def,

            have : leaves.redundant_in (gdt_tr1.mark_inactive_leaves env) :=
            begin
                unfold redundant_in,
                simp,
                have := sets_2 leaves_def.1 gdt_disjoint.2.2,
                split, { simp [*], },
                exact leaves_def.2,
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
        unfold Gdt.disjoint_leaves at gdt_disjoint,
        cases gdt_grd with gdt_grd var,
        case Grd.xgrd {
            cases c: xgrd_eval gdt_grd env with env',
            case option.some {
                simp [grd_eval_xgrd_some c],
                unfold redundant_in at leaves_def,
                simp only [Gdt.mark_inactive_leaves, Gdt.mark_inactive_leaves._match_1, c] at leaves_def,
                have : leaves.redundant_in (gdt_tr.mark_inactive_leaves env') :=
                begin
                    unfold redundant_in,
                    exact leaves_def,
                end,
                
                specialize gdt_ih gdt_disjoint env' this,
                unfold Gdt.remove_leaves,
                rw Gdt.eval_option_of_xgrd_eval_some c,
                exact gdt_ih,
            },
            case option.none {
                simp [grd_eval_xgrd_none c],
                unfold Gdt.remove_leaves,
                exact Gdt.eval_option_of_xgrd_eval_none c,
            },
        },
        case Grd.bang {
            cases c: is_bottom var env,
            case bool.tt {
                simp [grd_eval_bang_bottom c],
                simp [redundant_in, Gdt.leaves, Ant.leaves, Ant.inactive_leaves, Ant.critical_leaf_sets, Gdt.mark_inactive_leaves, c] at leaves_def,
                unfold Gdt.remove_leaves,
                apply Gdt.eval_option_of_is_bottom_tt c (remove_leaves_neq_none leaves_def.2),
            },
            case bool.ff {
                simp [redundant_in, Gdt.leaves, Gdt.mark_inactive_leaves, c, Ant.leaves, Ant.inactive_leaves, Ant.critical_leaf_sets] at leaves_def,
                have : redundant_in (gdt_tr.mark_inactive_leaves env) leaves, {
                    simp [redundant_in, Gdt.leaves, Gdt.mark_inactive_leaves, c, Ant.leaves, Ant.inactive_leaves, Ant.critical_leaf_sets],
                    exact leaves_def,
                },
                specialize gdt_ih gdt_disjoint env this,
                unfold Gdt.remove_leaves,
                simp [grd_eval_bang_not_bottom c],
                rw Gdt.eval_option_of_is_bottom_ff c,
                exact gdt_ih,
            },
        },
    },
end
