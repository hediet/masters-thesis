
import tactic
import data.finset

lemma to_finset_append { α: Type } [decidable_eq α] { l1: list α } { l2: list α }:
    (l1 ++ l2).to_finset = l1.to_finset ∪ l2.to_finset :=
begin
    induction l1;
    finish,
end

