def relation (x : Type) := x -> x -> Prop

def deterministic {t : Type} (r : relation t) :=
∀(x y1 y2 : t), r x y1 -> r x y2 -> y1 = y2

inductive multi {t : Type} {r : relation t} : relation t
| multi_refl : ∀{x : t}, multi x x
| multi_step : ∀{x y z : t}, r x y -> multi y z -> multi x z

def normal_form {T} (R : relation T) (t : T) := ¬∃t', R t t'
