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
lemma Ant.map_rhss { α β: Type } (ant: Ant α) (f: α → β): (ant.map f).rhss = ant.rhss :=
by induction ant; finish [Ant.rhss, Ant.rhss_list, Ant.map]

@[simp]
lemma Ant.map_disjoint_rhss_iff { α β: Type } { f: α → β } { ant: Ant α }: (ant.map f).disjoint_rhss ↔ ant.disjoint_rhss :=
by induction ant; { simp only [Ant.map, Ant.disjoint_rhss, *, Ant.map_rhss], }
