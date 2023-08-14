namespace Hidden

inductive List (α : Type u) where
| nil  : List α
| cons : α → List α → List α

namespace List

def append (as bs : List α) : List α :=
  match as with
  | nil       => bs
  | cons a as => cons a (append as bs)

theorem cons_append (a : α) (as bs : List α)
                    : append (cons a as) bs = cons a (append as bs) :=
  rfl

theorem append_nil (as : List α) : append as nil = as :=
  List.recOn (motive := fun x => append x nil = x) as
    rfl
    (fun a as ih => by simp [cons_append, ih])

theorem append_assoc (as bs cs : List α)
        : append (append as bs) cs = append as (append bs cs) :=
  List.recOn (motive := fun as => append (append as bs) cs = append as (append bs cs)) as
    rfl
    (fun a cs ih => by simp [cons_append, ih])

end List
end Hidden

-------------------------------