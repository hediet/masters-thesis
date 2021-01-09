import tactic
import ...definitions
import ..internal_definitions
import ..utils

variable [GuardModule]
open GuardModule

lemma Ant.map_associative { α β γ: Type } (f: β → γ) (g: α → β) (ant: Ant α):
    (ant.map g).map f = ant.map (f ∘ g) :=
by induction ant; simp [*, Ant.map]

@[simp]
lemma Ant.map_const { α β γ: Type } (c: γ) (g: α → β) (ant: Ant α):
    (ant.map g).map (λ x, c) = ant.map (λ x, c) :=
by rw Ant.map_associative

@[simp]
lemma Ant.map_id { α: Type } (ant: Ant α): ant.map id = ant :=
by induction ant; simp [Ant.map, *]

@[simp]
lemma Ant.map_leaves { α β: Type } (ant: Ant α) (f: α → β): (ant.map f).leaves = ant.leaves :=
by induction ant; finish [Ant.leaves, Ant.leaves_list, Ant.map]

@[simp]
lemma Ant.map_disjoint_leaves_iff { α β: Type } { f: α → β } { ant: Ant α }: (ant.map f).disjoint_leaves ↔ ant.disjoint_leaves :=
by induction ant; { simp only [Ant.map, Ant.disjoint_leaves, *, Ant.map_leaves], }
