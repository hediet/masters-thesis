import data.list

universe u

def Config (Q: Type u) := ℤ → Q

structure CA (Γ: Type u): Type (u+1) :=
  (Q : Type u)
  (embed: Γ → Q)
  (x: Q)
  (δ: Q → Q → Q → Q)
  (q_yes: Q)
  (q_no: Q)


inductive AB : Type u
| a
| b
open AB

def palindroms: set (list AB) := λ w, w.reverse = w



namespace CA

variable { Γ: Type u }
variable c: CA Γ

def L : set (list Γ) := λ w, (w.nth 0).map (λ x, c.embed x) = some c.x

def to_config (w: list Γ): Config c.Q :=
  λ n, if n ≥ 1 ∨ n ≤ w.length then w.

end CA



lemma foo: ∃ c: CA AB, c.L = palindroms := sorry
