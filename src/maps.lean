open function

def total_map (a : Type) : Type := string -> a

namespace total_map
  def empty {a : Type} (v : a) : total_map a := λx, v

  def update {a : Type} (x : string) (v : a) (m : total_map a) : total_map a :=
  λy, if x = y then v else m y

  def update_eq {a : Type} {x : string} {v : a} {m : total_map a} :
    (update x v m) x = v :=
  by { unfold update, simp [rfl] }

  def update_neq {a : Type} {x y : string} {v : a} {m : total_map a} (h : x ≠ y) :
    (update x v m) y = m y :=
  by {unfold update, simp [h] }

  def update_shadow {a : Type} {x : string} {v₁ v₂ : a} {m : total_map a} :
    update x v₂ (update x v₁ m) = update x v₂ m :=
  begin
    unfold update,
    apply funext,
    intro y,
    by_cases h : x = y,
    repeat { simp [h] },
  end

  def update_same {a : Type} {x : string} {v : a} {m : total_map a} :
    update x (m x) m = m :=
  begin
    unfold update,
    apply funext,
    intro y,
    by_cases h : x = y,
    repeat { simp [h] },
  end

  def update_permute {a : Type} {x y : string} {v₁ v₂ : a} {m : total_map a}
    (h : x ≠ y) :
    update x v₁ (update y v₂ m) = update y v₂ (update x v₁ m) :=
  begin
    unfold update,
    apply funext,
    intro z,
    by_cases hxz : x = z,
    { simp [hxz], rewrite symm hxz, simp [ne.symm h] },
    { simp [hxz], by_cases hyz : y = z; simp [hyz] },
  end
end total_map

def partial_map (a : Type) : Type := total_map (option a)

namespace partial_map
  def empty {a : Type} : partial_map a := total_map.empty none

  def update {a : Type} (x : string) (v : a) (m : partial_map a) :=
  total_map.update x (some v) m

  def apply_empty {a : Type} {x : string} : empty x = @none a := rfl

  def update_eq {a : Type} {x : string} {v : a} {m : partial_map a} :
    (update x v m) x = v := total_map.update_eq

  def update_neq {a : Type} {x y : string} {v : a} {m : partial_map a} (h : x ≠ y) :
    (update x v m) y = m y := total_map.update_neq h

  def update_shadow {a : Type} {x : string} {v₁ v₂ : a} {m : partial_map a} :
    update x v₂ (update x v₁ m) = update x v₂ m := total_map.update_shadow

  def update_same {a : Type} {x : string} {v : a} {m : partial_map a}
    (h : m x = some v) :
    update x v m = m :=
  by { unfold update, rewrite symm h, apply total_map.update_same, exact m x }

  def update_permute {a : Type} {x y : string} {v₁ v₂ : a} {m : partial_map a}
    (h : x ≠ y) :
    update x v₁ (update y v₂ m) = update y v₂ (update x v₁ m) :=
  total_map.update_permute h
end partial_map
