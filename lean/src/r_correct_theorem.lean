import .defs
variable [GuardModule]
open GuardModule

-- Every redundant leaf can be marked as inaccessible instead and
-- every inaccessible leaf can be marked as accessible instead without invalidating the theorem. This only weakens the analysis.

theorem main [decidable_eq Leaf] : ∀ gdt: Gdt, ∀ is_empty: Gs,
    (
        let ⟨ a, i, r ⟩ := ℛ is_empty.val $ 𝒜 gdt
        in
                -- Leaves that are redundant and neither accessible nor inaccessible can be removed without changing semantics.
                -- If all leaves are unique, a, i and r are disjoint.
                -- In that case, `((r.remove_all i).remove_all a` = `r`.
                -- If all leaves are equal, `((r.remove_all i).remove_all a` usually is the empty list.
                gdt_eval_option (remove_leaves ((r.remove_all i).remove_all a) gdt)
                = gdt_eval gdt
            ∧ 
                -- reachable leaves are accessible.
                -- Since R is clearly a partition for disjoint leaves,
                -- this also means that non-accessible leaves are unreachable.
                ∀ env: Env,
                    (match gdt_eval gdt env with
                    | (Result.leaf leaf) := leaf ∈ a
                    | _ := true
                    end : Prop)
        : Prop
    )
    -- We probably need 𝒜_eval for proving this.
    := sorry

