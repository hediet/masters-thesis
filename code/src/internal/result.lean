import tactic
import data.bool
import ..definitions
import .internal_definitions

variable [GuardModule]
open GuardModule

@[simp]
lemma Result.is_match_tt_neq_no_match (r: Result): r.is_match = tt ↔ r ≠ Result.no_match :=
by cases r; simp [Result.is_match]

@[simp]
lemma Result.is_match_ff_neq_no_match (r: Result): r.is_match = ff ↔ r = Result.no_match :=
by cases r; simp [Result.is_match]

@[simp]
lemma Result.is_match_neq_no_match (r: Result): r.is_match ↔ r ≠ Result.no_match :=
by cases r; simp [Result.is_match]

@[simp]
lemma Result.not_is_match_eq_no_match (r: Result): !r.is_match ↔ r = Result.no_match :=
by cases r; simp [Result.is_match]
