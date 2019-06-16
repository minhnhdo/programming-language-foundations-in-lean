import .logic
import .maps

inductive ty : Type
| bool : ty
| arrow : ty -> ty -> ty

open ty

inductive tm : Type
| var : string -> tm
| abs : string -> ty -> tm -> tm
| app : tm -> tm -> tm
| tru : tm
| fls : tm
| tst : tm -> tm -> tm -> tm

open tm

def x := "x"
def y := "y"
def z := "z"

def idB := abs x bool (var x)
def idBB := abs x (arrow bool bool) (var x)
def idBBBB := abs x (arrow (arrow bool bool) (arrow bool bool)) (var x)
def k := abs x bool (abs y bool (var x))
def notB := abs x bool (tst (var x) fls tru)

inductive value : tm -> Prop
| v_abs : ∀{x T t}, value (abs x T t)
| v_tru : value tru
| v_fls : value fls

open value

def subst (x : string) (s : tm) : tm -> tm
| (var y) := if x = y then s else var y
| (abs y T t1) := abs y T (if x = y then t1 else subst t1)
| (app t1 t2) := app (subst t1) (subst t2)
| tru := tru
| fls := fls
| (tst t1 t2 t3) := tst (subst t1) (subst t2) (subst t3)

notation `[` x `:=` s `]` t := subst x s t

inductive substi (s : tm) (x : string) : tm -> tm -> Prop
| s_var1 : substi (var x) s
| s_var2 {y : string} : y ≠ x -> substi (var y) (var y)
| s_abs1 {T : ty} {t : tm} : substi (abs x T t) (abs x T t)
| s_abs2 {y : string} {T : ty} {t t' : tm} :
    y ≠ x -> substi t t' -> substi (abs y T t) (abs y T t')
| s_app {t1 t1' t2 t2' : tm} :
    substi t1 t1' -> substi t2 t2' -> substi (app t1 t2) (app t1' t2')
| s_tru : substi tru tru
| s_fls : substi fls fls
| s_tst {t1 t1' t2 t2' t3 t3' : tm} :
    substi t1 t1' -> substi t2 t2' -> substi t3 t3' ->
    substi (tst t1 t2 t3) (tst t1' t2' t3')

theorem substi_correct : ∀ x s t t', ([x:=s]t) = t' ↔ substi s x t t' :=
begin
  intros,
  apply iff.intro,
  begin
    intro prf,
    induction prf,
    induction t,
    case tm.var: y
    begin
      unfold subst,
      cases decidable.em (x = y) with heq hne,
      { simp [heq], apply substi.s_var1 },
      { simp [hne], apply substi.s_var2, exact ne.symm hne },
    end,
    case tm.app: { apply substi.s_app, repeat { assumption } },
    case tm.abs: y T t
    begin
      unfold subst,
      cases decidable.em (x = y) with heq hne,
      { simp [heq], apply substi.s_abs1 },
      begin
        simp [hne],
        apply substi.s_abs2,
        exact ne.symm hne,
        assumption,
      end,
    end,
    case tm.tru: { apply substi.s_tru },
    case tm.fls: { apply substi.s_fls },
    case tm.tst: { apply substi.s_tst, repeat { assumption } },
  end,
  begin
    intro sub,
    induction sub,
    repeat { simp [*, subst]; /- s_var2 and s_abs2 -/ simp [ne.symm sub_a] },
  end,
end

inductive step : tm -> tm -> Prop
| st_appabs : ∀{x T t12 v2}, value v2 -> step (app (abs x T t12) v2) ([x:=v2]t12)
| st_app1 : ∀{t1 t1' t2}, step t1 t1' -> step (app t1 t2) (app t1' t2)
| st_app2 : ∀{v1 t2 t2'}, value v1 -> step t2 t2' -> step (app v1 t2) (app v1 t2')
| st_tsttru : ∀{t2 t3}, step (tst tru t2 t3) t2
| st_tstfls : ∀{t2 t3}, step (tst fls t2 t3) t3
| st_tst : ∀{t1 t1' t2 t3}, step t1 t1' -> step (tst t1 t2 t3) (tst t1' t2 t3)

open step

notation t ` -+> ` t' := step t t'

def multistep := @multi tm step

notation t ` -+>* ` t' := multistep t t'

open multi

example : app idBB idB -+>* idB :=
multi_step (st_appabs v_abs) multi_refl

example : app idBB (app idBB idB) -+>* idB :=
multi_step (st_app2 v_abs (st_appabs v_abs)) $
multi_step (st_appabs v_abs) $
multi_refl

example : app (app idBB notB) tru -+>* fls :=
multi_step (st_app1 (st_appabs v_abs)) $
multi_step (st_appabs v_tru) $
multi_step st_tsttru $
multi_refl

example : app idBB (app notB tru) -+>* fls :=
multi_step (st_app2 v_abs (st_appabs v_tru)) $
multi_step (st_app2 v_abs st_tsttru) $
multi_step (st_appabs v_fls) $
multi_refl

example : app (app idBBBB idBB) idB -+>* idB :=
multi_step (st_app1 (st_appabs v_abs)) $
multi_step (st_appabs v_abs) $
multi_refl

def context := partial_map ty

def context.empty : context := partial_map.empty

inductive has_type : context -> tm -> ty -> Prop
| t_var {gamma : context} {x T} :
    gamma x = some T -> has_type gamma (var x) T
| t_abs {gamma x T₁₁ T₁₂ t₁₂} :
    has_type (partial_map.update x T₁₁ gamma) t₁₂ T₁₂ ->
    has_type gamma (abs x T₁₁ t₁₂) (arrow T₁₁ T₁₂)
| t_app {gamma T₁₁ T₁₂ t₁ t₂} :
    has_type gamma t₁ (arrow T₁₁ T₁₂) ->
    has_type gamma t₂ T₁₁ ->
    has_type gamma (app t₁ t₂) T₁₂
| t_tru {gamma} : has_type gamma tru bool
| t_fls {gamma} : has_type gamma fls bool
| t_tst {gamma T t₁ t₂ t₃} :
    has_type gamma t₁ bool ->
    has_type gamma t₂ T ->
    has_type gamma t₃ T ->
    has_type gamma (tst t₁ t₂ t₃) T

open has_type

example : has_type context.empty (abs x bool (var x)) (arrow bool bool) :=
begin
  apply t_abs,
  apply t_var,
  reflexivity,
end

meta def auto_typing : tactic unit :=
tactic.repeat (   tactic.applyc ``t_tru
              <|> tactic.applyc ``t_fls
              <|> (tactic.applyc ``t_var >> tactic.reflexivity)
              <|> tactic.applyc ``t_abs
              <|> tactic.applyc ``t_tst )

example : has_type context.empty (abs x bool (var x)) (arrow bool bool) :=
by auto_typing

example {t : ty} : has_type context.empty
                            (abs x t
                              (abs y (arrow t t)
                                (app (var y) (app (var y) (var x)))))
                            (arrow t (arrow (arrow t t) t)) :=
t_abs (t_abs (t_app (t_var rfl) (t_app (t_var rfl) (t_var rfl))))

example : ∃t, has_type context.empty
                       (abs x (arrow bool bool)
                         (abs y (arrow bool bool)
                           (abs z bool
                             (app (var y) (app (var x) (var z))))))
                       t :=
⟨ arrow (arrow bool bool)
        (arrow (arrow bool bool)
               (arrow bool bool))
, t_abs (t_abs (t_abs (t_app (t_var rfl) (t_app (t_var rfl) (t_var rfl))))) ⟩

lemma arrow_no_confusion {t₁ t₂} : arrow t₁ t₂ ≠ t₁ :=
assume h : arrow t₁ t₂ = t₁,
begin
  induction t₁,
    case ty.bool: { apply @ty.no_confusion false _ _ h },
    case ty.arrow: t₃ t₄ ih₁ ih₂
    begin
      apply ih₁,
      injection h with h' h'',
      rewrite h'',
      exact h',
    end,
end

example : ¬∃s t, has_type context.empty (abs x s (app (var x) (var x))) t :=
assume ⟨ _, _, t_abs (t_app (t_var h₁) (t_var h₂)) ⟩,
have h : some (arrow _ _) = some _, from eq.trans (eq.symm h₁) h₂,
option.no_confusion h (assume h', arrow_no_confusion h')

inductive appears_free_in (x : string) : tm -> Prop
| afi_var : appears_free_in (var x)
| afi_abs {y t T} : y ≠ x -> appears_free_in t -> appears_free_in (abs y T t)
| afi_app1 {t₁ t₂} : appears_free_in t₁ -> appears_free_in (app t₁ t₂)
| afi_app2 {t₁ t₂} : appears_free_in t₂ -> appears_free_in (app t₁ t₂)
| afi_tst1 {t₁ t₂ t₃} : appears_free_in t₁ -> appears_free_in (tst t₁ t₂ t₃)
| afi_tst2 {t₁ t₂ t₃} : appears_free_in t₂ -> appears_free_in (tst t₁ t₂ t₃)
| afi_tst3 {t₁ t₂ t₃} : appears_free_in t₃ -> appears_free_in (tst t₁ t₂ t₃)

def closed (t : tm) := ∀x, ¬appears_free_in x t
