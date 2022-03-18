namespace ex

class has_add (α : Type*) :=
(add : α → α → α)

def add {α : Type*} [has_add α] : α → α → α := has_add.add

notation a ` + ` b := add a b

instance nat_has_add : has_add nat :=
⟨nat.add⟩

instance bool_has_add : has_add bool :=
⟨bor⟩

#check add 2 2    -- nat
#check tt + ff  -- bool

end ex