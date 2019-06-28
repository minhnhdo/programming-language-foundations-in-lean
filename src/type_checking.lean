import tactic
import .stlc

def type_check : context -> tm -> option ty
| gamma (tm.var x) := gamma x
| gamma (tm.abs x T t) := do
  T' <- type_check (partial_map.update x T gamma) t,
  return (ty.arrow T T')
| gamma (tm.app t₁ t₂) := do
  (ty.arrow T T') <- type_check gamma t₁ | failure,
  T₂ <- type_check gamma t₂,
  if T = T₂ then return T' else failure
| _ (tm.const _) := return ty.nat
| gamma (tm.prd t) := do
  ty.nat <- type_check gamma t | failure,
  return ty.nat
| gamma (tm.scc t) := do
  ty.nat <- type_check gamma t | failure,
  return ty.nat
| gamma (tm.mlt t₁ t₂) := do
  ty.nat <- type_check gamma t₁ | failure,
  ty.nat <- type_check gamma t₂ | failure,
  return ty.nat
| gamma (tm.iszro t) := do
  ty.nat <- type_check gamma t | failure,
  return ty.bool
| _ tm.tru := return ty.bool
| _ tm.fls := return ty.bool
| gamma (tm.tst t t₁ t₂) := do
  ty.bool <- type_check gamma t | failure,
  T <- type_check gamma t₁,
  T' <- type_check gamma t₂,
  if T = T' then return T else failure
| gamma (tm.let_ x t₁ t₂) := do
  T₁ <- type_check gamma t₁,
  T₂ <- type_check (partial_map.update x T₁ gamma) t₂,
  return T₂
| gamma (tm.pair t₁ t₂) := do
  T₁ <- type_check gamma t₁,
  T₂ <- type_check gamma t₂,
  return (ty.prod T₁ T₂)
| gamma (tm.fst t) := do
  (ty.prod T₁ _) <- type_check gamma t | failure,
  return T₁
| gamma (tm.snd t) := do
  (ty.prod _ T₂) <- type_check gamma t | failure,
  return T₂
| _ tm.unit := return ty.unit
| gamma (tm.inl T₂ t) := do
  T₁ <- type_check gamma t,
  return (ty.sum T₁ T₂)
| gamma (tm.inr T₁ t) := do
  T₂ <- type_check gamma t,
  return (ty.sum T₁ T₂)
| gamma (tm.scase t x t₁ y t₂) := do
  (ty.sum T₁ T₂) <- type_check gamma t | failure,
  T <- type_check (partial_map.update x T₁ gamma) t₁,
  T' <- type_check (partial_map.update y T₂ gamma) t₂,
  if T = T' then return T else failure
| _ (tm.nil T) := return (ty.list T)
| gamma (tm.cons t₁ t₂) := do
  T <- type_check gamma t₁,
  (ty.list T') <- type_check gamma t₂ | failure,
  if T = T' then return (ty.list T) else failure
| gamma (tm.lcase t t₁ y z t₂) := do
  (ty.list T) <- type_check gamma t | failure,
  T' <- type_check gamma t₁,
  T'' <- type_check (partial_map.update z (ty.list T) $
                     partial_map.update y T gamma)
                    t₂,
  if T' = T'' then return T' else failure
| gamma (tm.fix t) := do
  (ty.arrow T T') <- type_check gamma t | failure,
  if T = T' then return T else failure

theorem type_checking_sound {t} :
  ∀{gamma T}, type_check gamma t = some T -> has_type gamma t T :=
begin
  induction t,
    repeat { intros _ _ h, simp [type_check, return, pure] at h },
    case tm.var: { apply has_type.t_var, assumption },
    case tm.abs: _ _ _ ih {
      rcases h with ⟨_, h', h''⟩,
      rewrite <-h'',
      exact has_type.t_abs (ih h'),
    },
    case tm.app: t₁ t₂ ih₁ ih₂ {
      rcases h with ⟨T', h', h''⟩,
      cases e₁ : type_check gamma t₁,
        { cases eq.trans (symm e₁) h', },
        { cases e₂ : type_check gamma t₂,
            case option.none: { cases T'; rewrite e₂ at h''; cases h'' },
            case option.some: {
              cases T',
                case ty.arrow: T₁' T₂ {
                  simp [type_check, return, pure] at h'',
                  rcases h'' with ⟨T₁, he₂, he₂'⟩,
                  by_cases ht : T₁' = T₁,
                    { simp [ht] at he₂',
                      rewrite <-he₂',
                      rewrite <-ht at he₂,
                      exact has_type.t_app (ih₁ h') (ih₂ he₂) },
                    { simp [ht] at he₂', cases he₂' },
                },
                repeat { cases h'' },
            } },
    },
    case tm.const: { rewrite <-h, exact has_type.t_const },
    case tm.prd: _ ih {
      rcases h with ⟨T', h', h''⟩,
      cases T',
        case ty.nat: {
          simp [type_check, return, pure] at h'',
          rewrite <-h'',
          exact has_type.t_prd (ih h'),
        },
        repeat { cases h'' },
    },
    case tm.scc: _ ih {
      rcases h with ⟨T', h', h''⟩,
      cases T',
        case ty.nat: {
          simp [type_check, return, pure] at h'',
          rewrite <-h'',
          exact has_type.t_scc (ih h'),
        },
        repeat { cases h'' },
    },
    case tm.mlt: t₁ t₂ ih₁ ih₂ {
      rcases h with ⟨T₁, h', h''⟩,
      cases e₁ : type_check gamma t₁,
        { cases eq.trans (symm e₁) h', },
        { cases e₂ : type_check gamma t₂,
          case option.none: { cases T₁; rewrite e₂ at h''; cases h'' },
          case option.some: {
            cases T₁,
            case ty.nat: {
              simp [type_check, return, pure] at h'',
              rcases h'' with ⟨T₂, he₂, he₂'⟩,
              cases T₂,
                case ty.nat: {
                  simp [type_check, return, pure] at he₂',
                  rewrite <-he₂',
                  exact has_type.t_mlt (ih₁ h') (ih₂ he₂),
                },
                repeat { cases he₂' },
            },
            repeat { cases h'' },
          } },
    },
    case tm.iszro: _ ih {
      rcases h with ⟨T', h', h''⟩,
      cases T',
        case ty.nat: {
          simp [type_check, return, pure] at h'',
          rewrite <-h'',
          exact has_type.t_iszro (ih h'),
        },
        repeat { cases h'' },
    },
    case tm.tru: { rewrite <-h, exact has_type.t_tru },
    case tm.fls: { rewrite <-h, exact has_type.t_fls },
    case tm.tst: t t₁ t₂ ih ih₁ ih₂ {
      rcases h with ⟨T, h', h''⟩,
      cases T,
        case ty.bool: {
          simp [type_check, return, pure] at h'',
          rcases h'' with ⟨T₁, h₁, T₂, h₂, ht⟩,
          by_cases ht' : T₁ = T₂,
            { simp [ht'] at ht,
              rewrite <-ht,
              rewrite ht' at h₁,
              exact has_type.t_tst (ih h') (ih₁ h₁) (ih₂ h₂) },
            { simp [ht'] at ht, cases ht },
        },
        repeat { cases h'' },
    },
    case tm.let_: _ _ _ ih₁ ih₂ {
      rcases h with ⟨_, h', h''⟩,
      exact has_type.t_let (ih₁ h') (ih₂ h''),
    },
    case tm.pair: _ _ ih₁ ih₂ {
      rcases h with ⟨_, h₁, _, h₂, h''⟩,
      rewrite <-h'',
      exact has_type.t_pair (ih₁ h₁) (ih₂ h₂),
    },
    case tm.fst: _ ih {
      rcases h with ⟨T', h', h''⟩,
      cases T',
        case ty.prod: T₁ T₂ {
          simp [type_check, return, pure] at h'',
          rewrite <-h'',
          exact has_type.t_fst (ih h'),
        },
        repeat { cases h'' },
    },
    case tm.snd: _ ih {
      rcases h with ⟨T', h', h''⟩,
        cases T',
          case ty.prod: T₁ T₂ {
            simp [type_check, return, pure] at h'',
            rewrite <-h'',
            exact has_type.t_snd (ih h'),
          },
          repeat { cases h'' },
    },
    case tm.unit: { rewrite <-h, exact has_type.t_unit },
    case tm.inl: _ _ ih {
      rcases h with ⟨_, h', h''⟩,
      rewrite <-h'',
      exact has_type.t_inl (ih h'),
    },
    case tm.inr: _ _ ih {
      rcases h with ⟨_, h', h''⟩,
      rewrite <-h'',
      exact has_type.t_inr (ih h'),
    },
    case tm.scase: _ _ _ _ _ ih ih₁ ih₂ {
      rcases h with ⟨T, h, h'⟩,
      cases T,
        case ty.sum: T₁ T₂ {
          simp [type_check] at h',
          rcases h' with ⟨T₁, h₁, T₂, h₂, h''⟩,
          by_cases ht : T₁ = T₂,
            { simp [ht, return, pure] at h'',
              rewrite ht at h₁,
              rewrite h'' at h₁ h₂,
              exact has_type.t_scase (ih h) (ih₁ h₁) (ih₂ h₂) },
            { simp [ht] at h'', cases h'' },
        },
        repeat { cases h' },
    },
    case tm.nil: { rewrite <-h, exact has_type.t_nil },
    case tm.cons: _ _ ih₁ ih₂ {
      rcases h with ⟨T₁, h₁, T₂, h₂, h'⟩,
      cases T₂,
        case ty.list: T₁' {
          simp [type_check, return, pure] at h',
          by_cases ht : T₁ = T₁',
            { simp [ht] at h',
              rewrite <-h',
              rewrite ht at h₁,
              exact has_type.t_cons (ih₁ h₁) (ih₂ h₂) },
            { simp [ht] at h', cases h' },
        },
        repeat { cases h' },
    },
    case tm.lcase: _ _ _ _ _ ih ih₁ ih₂ {
      rcases h with ⟨T, h, h'⟩,
      cases T,
        case ty.list: T' {
          simp [type_check, return, pure] at h',
          rcases h' with ⟨T₁, h₁, T₂, h₂, h''⟩,
          by_cases ht : T₁ = T₂,
            { simp [ht] at h'',
              rewrite ht at h₁,
              rewrite <-h'',
              exact has_type.t_lcase (ih h) (ih₁ h₁) (ih₂ h₂) },
            { simp [ht] at h'', cases h'' },
        },
        repeat { cases h' },
    },
    case tm.fix: _ ih {
      rcases h with ⟨T', h', h''⟩,
      cases T',
        case ty.arrow: T₁ T₂ {
          simp [type_check, return, pure] at h'',
          by_cases ht : T₁ = T₂,
            { simp [ht] at h'',
              rewrite ht at h',
              rewrite <-h'',
              exact has_type.t_fix (ih h') },
            { simp [ht] at h'', cases h'' },
        },
        repeat { cases h'' },
    },
end

theorem type_checking_complete {gamma t T} (ht : has_type gamma t T) :
  type_check gamma t = some T :=
by { induction ht; simp [*, type_check, return, pure] }
