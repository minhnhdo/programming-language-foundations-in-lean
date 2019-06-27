import .stlc

def type_check : context -> tm -> option ty
| gamma (tm.var x) := gamma x
| gamma (tm.abs x T t) := do
  T' <- type_check (partial_map.update x T gamma) t,
  return (ty.arrow T T')
| gamma (tm.app t₁ t₂) :=
  match type_check gamma t₁, type_check gamma t₂ with
  | (some (ty.arrow T T')), (some T₂) := if T = T₂ then some T' else none
  | _, _ := none
  end
| _ (tm.const _) := some ty.nat
| gamma (tm.prd t) := do
  ty.nat <- type_check gamma t | none,
  return ty.nat
| gamma (tm.scc t) := do
  ty.nat <- type_check gamma t | none,
  return ty.nat
| gamma (tm.mlt t₁ t₂) := do
  ty.nat <- type_check gamma t₁ | none,
  ty.nat <- type_check gamma t₂ | none,
  return ty.nat
| gamma (tm.iszro t) := do
  ty.nat <- type_check gamma t | none,
  return ty.bool
| _ tm.tru := some ty.bool
| _ tm.fls := some ty.bool
| gamma (tm.tst t t₁ t₂) := do
  ty.bool <- type_check gamma t | none,
  T <- type_check gamma t₁,
  T' <- type_check gamma t₁,
  if T = T' then return T else none
| gamma (tm.let_ x t₁ t₂) := do
  T₁ <- type_check gamma t₁,
  T₂ <- type_check (partial_map.update x T₁ gamma) t₂,
  return T₂
| gamma (tm.pair t₁ t₂) := do
  T₁ <- type_check gamma t₁,
  T₂ <- type_check gamma t₂,
  return (ty.prod T₁ T₂)
| gamma (tm.fst t) := do
  (ty.prod T₁ _) <- type_check gamma t | none,
  return T₁
| gamma (tm.snd t) := do
  (ty.prod _ T₂) <- type_check gamma t | none,
  return T₂
| _ tm.unit := some ty.unit
| gamma (tm.inl T₂ t) := do
  T₁ <- type_check gamma t,
  return (ty.sum T₁ T₂)
| gamma (tm.inr T₁ t) := do
  T₂ <- type_check gamma t,
  return (ty.sum T₁ T₂)
| gamma (tm.scase t x t₁ y t₂) := do
  (ty.sum T₁ T₂) <- type_check gamma t | none,
  T <- type_check (partial_map.update x T₁ gamma) t₁,
  T' <- type_check (partial_map.update y T₂ gamma) t₂,
  if T = T' then some T else none
| _ (tm.nil T) := some (ty.list T)
| gamma (tm.cons t₁ t₂) := do
  T <- type_check gamma t₁,
  (ty.list T') <- type_check gamma t₂ | none,
  if T = T' then some (ty.list T) else none
| gamma (tm.lcase t t₁ y z t₂) := do
  (ty.list T) <- type_check gamma t | none,
  T' <- type_check gamma t₁,
  T'' <- type_check (partial_map.update z (ty.list T) $
                     partial_map.update y T gamma)
                    t₂,
  if T' = T'' then some T' else none
| gamma (tm.fix t) := do
  (ty.arrow T T') <- type_check gamma t | none,
  if T = T' then some T else none

theorem type_checking_complete {gamma t T} (ht : has_type gamma t T) :
  type_check gamma t = some T :=
by { induction ht; simp [*, type_check, (>>=), option.bind, return, pure] }
