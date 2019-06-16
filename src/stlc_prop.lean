import tactic
import .stlc

open has_type
open step
open tm
open ty
open value

lemma abs_not_has_type_bool {gamma x T t} : ¬(has_type gamma (abs x T t) bool).

lemma tru_not_has_type_arrow {gamma T₁ T₂} : ¬(has_type gamma tru (arrow T₁ T₂)).

lemma fls_not_has_type_arrow {gamma T₁ T₂} : ¬(has_type gamma fls (arrow T₁ T₂)).

lemma cannonical_forms_bool {t}
  (ht : has_type context.empty t bool) (v : value t) :
  t = tru ∨ t = fls :=
begin
  induction v,
    case v_abs: { exact false.elim (abs_not_has_type_bool ht) },
    case v_tru: { left, constructor },
    case v_fls: { right, constructor },
end

lemma cannonical_forms_fun {t T₁ T₂}
  (ht : has_type context.empty t (arrow T₁ T₂)) (v : value t) :
  ∃x T u, t = abs x T u :=
begin
  induction v,
    case v_abs : x T t {
      existsi x,
      existsi T,
      existsi t,
      reflexivity,
    },
    case v_tru : { exact false.elim (tru_not_has_type_arrow ht) },
    case v_fls : { exact false.elim (fls_not_has_type_arrow ht) },
end

lemma empty_context_neq_some {x T} : context.empty x ≠ some T.

lemma var_not_has_type_empty_context {x T} : ¬(has_type context.empty (var x) T)
| (t_var h) := false.elim (empty_context_neq_some h)

lemma app_has_type {gamma t₁ t₂ T₂} :
  has_type gamma (app t₁ t₂) T₂ ->
  ∃T₁, has_type gamma t₁ (arrow T₁ T₂) ∧ has_type gamma t₂ T₁
| (@t_app _ T₁ _ _ _ ht₁ ht₂) := ⟨T₁, ht₁, ht₂⟩

lemma tst_has_type {gamma t₁ t₂ t₃ T} :
  has_type gamma (tst t₁ t₂ t₃) T ->
  has_type gamma t₁ bool ∧ has_type gamma t₂ T ∧ has_type gamma t₃ T
| (t_tst ht₁ ht₂ ht₃) := ⟨ht₁, ht₂, ht₃⟩

theorem progress {t T} :
  has_type context.empty t T -> value t ∨ ∃t', t -+> t' :=
begin
  generalize h : context.empty = e,
  intro ht,
  induction ht,
    case has_type.t_var: e s t ht { rewrite <-h at ht, cases ht },
    case has_type.t_abs: { left, constructor },
    case has_type.t_app: e t₁ t₂ m₁ m₂ ht₁ ht₂ ih₃ ih₄ {
      rcases ih₃ h with v₁ | ⟨t₁', s₁⟩,
        begin
          rcases ih₄ h with v₂ | ⟨t₂', s₂⟩,
            { cases v₁; cases ht₁, right, existsi _, exact step.st_appabs v₂ },
            { right, existsi _, exact step.st_app2 v₁ s₂ },
        end,
        begin
          right,
          existsi _,
          exact step.st_app1 s₁,
        end,
    },
    case has_type.t_tru: { left, constructor },
    case has_type.t_fls: { left, constructor },
    case has_type.t_tst: e T t₁ t₂ t₃ ht₁ ht₂ ht₃ ih₁ ih₂ ih₃ {
      rcases ih₁ h with v₁ | ⟨t₁', s₁⟩,
        begin
          rewrite <-h at ht₁,
          cases cannonical_forms_bool ht₁ v₁ with h_tru h_fls,
            { rewrite h_tru, right, existsi _, exact st_tsttru },
            { rewrite h_fls, right, existsi _, exact st_tstfls },
        end,
        begin
          right,
          existsi _,
          exact st_tst s₁,
        end,
    },
end
