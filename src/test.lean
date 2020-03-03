variable {α : Type}
inductive foo : α → Type
| one (a : α) : foo a
| cons (a b : α) (f : foo b) : foo a


def length : Π (a : α) (f : foo a), ℕ
| _ (foo.one a) := 1
| _ (foo.cons a b f) := 1 + length b f