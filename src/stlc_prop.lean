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
    case has_type.t_app: e T₁ T₂ t₁ t₂ ht₁ ht₂ ih₁ ih₂ {
      rewrite <-h at ht₁,
      rewrite <-h at ht₂,
      cases ih₁ h with v₁ st₁,
        begin
          rcase cannonical_forms_fun ht₁ v₁ with e',
          -- cases e' with T e'',
          -- cases e'' with u h₁,
          -- rewrite h₁,
          -- cases ih₂ h with v₂ st₂,
          --   begin
          --     right,
          --     existsi subst x t₂ u,
          --     exact st_appabs v₂,
          --   end,
          --   begin
          --   end,
        end,
    },
    case has_type.t_tru: { left, constructor },
    case has_type.t_fls: { left, constructor },
    case has_type.t_tst: e T t₁ t₂ t₃ ht₁ ht₂ ht₃ ih₁ ih₂ ih₃ {
      rewrite <-h at ht₁,
      cases ih₁ h with v₁ st₁,
        begin
          cases cannonical_forms_bool ht₁ v₁ with h_tru h_fls,
            { rewrite h_tru, right, existsi t₂, exact st_tsttru },
            { rewrite h_fls, right, existsi t₃, exact st_tstfls },
        end,
        begin
          cases st₁ with t₁' s₁,
          right,
          existsi tst t₁' t₂ t₃,
          exact st_tst s₁,
        end,
    },
end
