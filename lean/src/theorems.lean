import .definitions
import .internal.U
import .internal.R
import .internal.A
import .internal.internal_definitions
import .internal.R_red_removable
import .internal.R_acc_mem_of_reachable

variable [GuardModule]
open GuardModule

theorem 𝒰_semantic: ∀ gdt: Gdt, ∀ env: Env,
        (𝒰 gdt).eval env ↔ (gdt.eval env = Result.no_match) :=
begin
    assume gdt env,
    rw ←@U_eq_𝒰,
    simp [U_semantic],
end

theorem ℛ_semantic : ∀ can_prove_empty: Gs, ∀ gdt: Gdt, gdt.disjoint_leaves → 
    (
        let ⟨ a, i, r ⟩ := ℛ can_prove_empty.val (𝒜 gdt)
        in
                -- Reachable leaves are accessible and neither inaccessible nor redundant.
                (∀ env: Env, ∀ leaf: Leaf,
                    gdt.eval env = Result.leaf leaf
                      → leaf ∈ a \ (i ++ r)
                )
            ∧
                -- Redundant leaves can be removed without changing semantics.
                Gdt.eval_option (gdt.remove_leaves r.to_finset)
                = gdt.eval

        : Prop
    )
    :=
begin
    assume can_prove_empty gdt gdt_disjoint,
    cases c: ℛ can_prove_empty.val (𝒜 gdt) with a i_r,
    cases i_r with i r,
    dsimp only,

    rw ←R_eq_ℛ at c,
    unfold LeafPartition.to_triple at c,
    set p := R (Ant.map can_prove_empty.val (𝒜 gdt)) with p_def,
    cases c,

    
    have Agdt_def := eq.symm (Ant.mark_inactive_leaves_eq_of_eval_leaves_eq (A_eq_𝒜 gdt)),
    

    split, {
        assume env leaf h,
        replace Agdt_def := function.funext_iff.1 Agdt_def env,
        exact R_acc_mem_of_reachable gdt_disjoint can_prove_empty Agdt_def h p_def,
    }, {
        have := R_red_removable can_prove_empty gdt_disjoint Agdt_def,
        rw ←p_def at this,
        exact this,
    },
end
