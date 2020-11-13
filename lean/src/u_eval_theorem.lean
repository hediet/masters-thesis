import tactic
import .defs
import .lemmas

variable [GuardModule]
open GuardModule

def as_no_match : Result → option Env
| (Result.no_match env) := some env
| (Result.diverged) := none
| (Result.leaf _) := none


-- Uncovered refinement types capture all values that are not covered.
-- This theorem might be easier to show for 𝒰' rather than 𝒰.
theorem 𝒰_eval :
    ∀ gdt: Gdt, ∀ env: Env,
        as_no_match (gdt_eval gdt env) = Φ_eval (𝒰 gdt) env := 
begin
    assume gdt: Gdt,
    assume env: Env,

    rw 𝒰_𝒰'_equiv,
 
    induction gdt with leaf generalizing env,

    case Gdt.leaf {
        unfold gdt_eval,
        unfold 𝒰',
        unfold Φ_eval,
        finish,
    },
  
    case Gdt.branch {
        unfold 𝒰',
        unfold gdt_eval,
        unfold Φ_eval,
        simp,

        cases c1: (Φ_eval (𝒰' gdt_tr1) env),

        all_goals {
            rw Φ_eval._match_3,
            specialize gdt_ih_tr1 env,
            rw c1 at gdt_ih_tr1,
            cases gdt_eval gdt_tr1 env,
        },

        all_goals {
            rw gdt_eval._match_1,
        },
        repeat {
            finish,
        },

        rw as_no_match at gdt_ih_tr1,
        simp at gdt_ih_tr1,
        finish
    },

    case Gdt.grd {
        cases gdt_grd,
        all_goals {
            unfold 𝒰',
            unfold gdt_eval,
            unfold Φ_eval,
            simp
        },

        {
            cases (xgrd_eval gdt_grd env),
            all_goals {
                rw gdt_eval._match_2,
                rw Φ_eval._match_1,
                rw Φ_eval._match_3,
                rw Φ_eval._match_2,
            },
            {
                rw as_no_match,
            },
            {
                specialize gdt_ih val,
                exact gdt_ih,
            }
        },

        {
            cases (is_bottom gdt_grd env),
            all_goals {
                simp,
                unfold Φ_eval._match_3,
            },
            {
                specialize gdt_ih env,
                exact gdt_ih,
            },
            {
                finish,
            }
        }
    }
end
