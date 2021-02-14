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

theorem ℛ_semantic : ∀ can_prove_empty: CorrectCanProveEmpty, ∀ gdt: Gdt, gdt.disjoint_rhss → 
    (
        let ⟨ a, i, r ⟩ := ℛ can_prove_empty.val (𝒜 gdt)
        in
                -- Reachable rhss are accessible and neither inaccessible nor redundant.
                (∀ env: Env, ∀ rhs: Rhs,
                    gdt.eval env = Result.value rhs
                      → rhs ∈ a \ (i ++ r)
                )
            ∧
                -- Redundant rhss can be removed without changing semantics.
                Gdt.eval_option (gdt.remove_rhss r.to_finset)
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
    unfold RhsPartition.to_triple at c,
    set p := R (Ant.map can_prove_empty.val (𝒜 gdt)) with p_def,
    cases c,

    have Agdt_def := eq.symm (Ant.mark_inactive_rhss_eq_of_eval_rhss_eq (A_eq_𝒜 gdt)),
    
    split, {
        assume env rhs h,
        replace Agdt_def := function.funext_iff.1 Agdt_def env,
        exact R_acc_mem_of_reachable gdt_disjoint can_prove_empty Agdt_def h p_def,
    }, {
        have := R_red_removable can_prove_empty gdt_disjoint Agdt_def,
        rw ←p_def at this,
        exact this,
    },
end

theorem 𝒰𝒜_acc_eq (acc: Φ → Φ) (gdt: Gdt): 𝒰𝒜_acc acc gdt = (𝒰_acc acc gdt, 𝒜_acc acc gdt) :=
by induction gdt generalizing acc; try { cases gdt_grd }; simp [𝒰𝒜_acc, 𝒰_acc, 𝒜_acc, *]
