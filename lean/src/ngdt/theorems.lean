import .defs
variable [NGuardModule]
open NGuardModule

-- Reduction to Guard Trees maintains semantic.
-- This is a very important statement, as it allows to use the theory of refinement types
-- to understand non-strict guard trees.
theorem ngdt_eval_eq_gdt_eval :
        ngdt_eval = gdt_eval ∘ ngdt_to_gdt :=
begin
    funext gdt,
    funext env,
    rw function.comp,
    simp,
    induction gdt generalizing env,

    case NGdt.leaf {
        unfold ngdt_to_gdt,
        unfold ngdt_eval,
        unfold gdt_eval
    },

    case NGdt.branch {
        unfold ngdt_to_gdt,
        unfold ngdt_eval,
        unfold gdt_eval,

        rw ←gdt_ih_a,
        rw ←gdt_ih_a_1,
        
        cases ngdt_eval gdt_a env,
        all_goals {
            cases ngdt_eval gdt_a_1 env,
        },
        all_goals {
            unfold ngdt_eval._match_1,
            unfold gdt_eval._match_1,
        }
    },

    case NGdt.grd {
        cases gdt_a,
        all_goals {
            rw ngdt_to_gdt,
            unfold ngdt_eval,
            unfold gdt_eval,
            rw ←gdt_ih,
        },
        
        unfold GuardModule.grd_eval,
    }
    --case NGdt.
    --rw ngdt_to_gdt,

end


-- Every redundant leaf can be marked as inaccessible instead and
-- every inaccessible leaf can be marked as accessible instead without invalidating the theorem. This only weakens the analysis.

theorem main [decidable_eq Leaf] : ∀ ngdt: NGdt, ∀ is_empty: Gs,
    (
        let ⟨ a, i, r ⟩ := ℛ is_empty.val $ 𝒜 $ ngdt_to_gdt ngdt
        in
                -- Leaves that are redundant and neither accessible nor inaccessible can be removed without changing semantics.
                -- If all leaves are unique, a, i and r are disjoint.
                -- In that case, `((r.remove_all i).remove_all a` = `r`.
                -- If all leaves are equal, `((r.remove_all i).remove_all a` usually is the empty list.
                ngdt_eval_option (remove_leaves ((r.remove_all i).remove_all a) ngdt)
                = ngdt_eval ngdt
            ∧ 
                -- reachable leaves are accessible.
                -- Since R is clearly a partition for disjoint leaves,
                -- this also means that non-accessible leaves are unreachable.
                ∀ env: Env,
                    (match ngdt_eval ngdt env with
                    | (some ⟨ _, NLeaf.leaf leaf ⟩) := leaf ∈ a
                    | _ := true
                    end : Prop)
        : Prop
    )
    -- We probably need 𝒜_eval for proving this.
    := sorry

