import .defs

variable [GuardModule]
open GuardModule

-- Uncovered refinement types capture all values that are not covered.
-- This theorem might be easier to show for 𝒰' rather than 𝒰.
theorem 𝒰_eval :
    ∀ env: Env, ∀ gdt: Gdt,
        (gdt_eval gdt env ≠ none) ↔ (Φ_eval (𝒰 gdt) env = none)
    := sorry

