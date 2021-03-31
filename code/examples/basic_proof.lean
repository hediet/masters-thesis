
inductive my_nat : Type
| zero : my_nat
| succ : my_nat → my_nat

#check my_nat.succ my_nat.zero
#check my_nat.zero.succ -- (using dot notation)

def my_nat.add : my_nat → my_nat → my_nat
| my_nat.zero b := b
| (my_nat.succ a) b := (a.add b).succ

def my_nat.add_zero : Π a: my_nat, a.add my_nat.zero = a :=
    @my_nat.rec
        -- Induction Hypothesis
        (λ a, a.add my_nat.zero = a)
        -- Case Zero
        (my_nat.add.equations._eqn_1 my_nat.zero)
        -- Case Succ
        (λ a h,
            @eq.subst my_nat
                (λ x, (my_nat.succ a).add my_nat.zero = x.succ)
                (a.add my_nat.zero)
                a
                h
                (my_nat.add.equations._eqn_2 a my_nat.zero)
        )

def my_nat.add_zero' (a: my_nat): a.add my_nat.zero = a :=
begin
    induction a,
    { refl, },
    { simp [my_nat.add, *], },
end

--( my_nat.zero.add my_nat.zero = my_nat.zero)