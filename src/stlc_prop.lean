import tactic
import .stlc

open appears_free_in
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

theorem progress' :
  ∀{t T}, has_type context.empty t T -> value t ∨ ∃t', t -+> t' :=
begin
  intro t,
  induction t,
    case tm.var: { intros _ ht, cases ht, cases ht_a },
    case tm.abs: { intros, left, constructor },
    case tm.app: _ _ ih₁ ih₂ {
      intros _ ht,
      cases ht,
      rcases ih₁ ht_a with v₁ | ⟨_, s₁⟩,
        { rcases ih₂ ht_a_1 with v₂ | ⟨_, s₂⟩,
            { rcases cannonical_forms_fun ht_a v₁ with ⟨_, _, _, h⟩,
              rewrite h,
              right,
              existsi _,
              exact st_appabs v₂ },
            { right, existsi _, exact st_app2 v₁ s₂ } },
        { right, existsi _, exact st_app1 s₁ },
    },
    case tm.tru: { intros, left, constructor },
    case tm.fls: { intros, left, constructor },
    case tm.tst: _ _ _ ih₁ ih₂ ih₃ {
      intros _ ht,
      cases ht,
      rcases ih₁ ht_a with v₁ | ⟨_, s₁⟩,
        { cases cannonical_forms_bool ht_a v₁ with h_tru h_fls,
            { rewrite h_tru, right, existsi _, exact st_tsttru },
            { rewrite h_fls, right, existsi _, exact st_tstfls } },
        { right, existsi _, apply st_tst s₁ },
    },
end

lemma free_in_context {x t} (afi : appears_free_in x t) :
  ∀{gamma T}, has_type gamma t T -> ∃T', gamma x = some T' :=
begin
  induction afi,
    case appears_free_in.afi_var: {
      intros gamma T ht,
      cases ht,
      existsi T,
      exact ht_a,
    },
    case appears_free_in.afi_abs: _ _ _ hne _ ih {
      intros gamma T ht,
      cases ht with,
      rcases ih ht_a with ⟨T', h'⟩,
      existsi T',
      rewrite partial_map.update_neq hne at h',
      exact h',
    },
    case appears_free_in.afi_app1: _ _ _ ih {
      intros gamma T ht,
      cases ht,
      exact ih ht_a,
    },
    case appears_free_in.afi_app2: _ _ _ ih {
      intros gamma T ht,
      cases ht,
      exact ih ht_a_1,
    },
    case appears_free_in.afi_tst1: _ _ _ _ ih {
      intros gamma T ht,
      cases ht,
      exact ih ht_a,
    },
    case appears_free_in.afi_tst2: _ _ _ _ ih {
      intros gamma T ht,
      cases ht,
      exact ih ht_a_1,
    },
    case appears_free_in.afi_tst3: _ _ _ _ ih {
      intros gamma T ht,
      cases ht,
      exact ih ht_a_2,
    },
end

lemma typable_empty__closed {t T} : has_type context.empty t T -> closed t :=
begin
  intros ht x afi,
  rcases free_in_context afi ht with ⟨_, h⟩,
  cases h,
end

lemma context_invariance {gamma t T} (ht : has_type gamma t T) :
  ∀{gamma' : context},
  (∀{x}, appears_free_in x t -> gamma x = gamma' x) -> has_type gamma' t T :=
begin
  induction ht,
    case has_type.t_var: _ x _ h {
      intros _ f,
      apply t_var,
      rewrite <-f (afi_var x),
      exact h,
    },
    case has_type.t_abs: _ x T₁ _ _ _ ih {
      intros gamma' f,
      apply t_abs,
      apply @ih (partial_map.update x T₁ gamma'),
      intros y afi,
      by_cases h : x = y,
      repeat {
        simp [h, partial_map.update, total_map.update];
        exact f (afi_abs h afi)
      },
    },
    case has_type.t_app: _ _ _ _ _ _ _ ih₁ ih₂ {
      intros _ f,
      apply t_app,
        { apply ih₁, intros x afi₁, apply @f x, exact afi_app1 afi₁ },
        { apply ih₂, intros x afi₂, apply @f x, exact afi_app2 afi₂ },
    },
    case has_type.t_tru: { intros x f, apply t_tru },
    case has_type.t_fls: { intros x f, apply t_fls },
    case has_type.t_tst: gamma _ _ _ _ _ _ _ ih₁ ih₂ ih₃ {
      intros _ f,
      apply t_tst,
        { apply ih₁, intros x afi₁, apply @f x, exact afi_tst1 afi₁ },
        { apply ih₂, intros x afi₂, apply @f x, exact afi_tst2 afi₂ },
        { apply ih₃, intros x afi₃, apply @f x, exact afi_tst3 afi₃ },
    },
end

lemma substitution_preserves_typing {x U v} :
  ∀{t T gamma},
  has_type (partial_map.update x U gamma) t T -> has_type context.empty v U ->
  has_type gamma ([x:=v]t) T :=
begin
  intro t,
  induction t,
    case tm.var: y {
      intros _ _ ht_t ht_v,
      by_cases h : x = y,
        begin
          rewrite h at ht_t,
          cases ht_t,
          simp at ht_t_a,
          simp [h, ht_t_a, subst],
          rewrite ht_t_a at ht_v,
          apply context_invariance ht_v,
          intros z afi,
          apply false.elim,
          exact typable_empty__closed ht_v z afi,
        end,
        begin
          cases ht_t,
          simp [h] at ht_t_a,
          simp [h, subst],
          exact t_var ht_t_a,
        end,
    },
    case tm.abs: y T' t ih {
      intros T gamma ht_t ht_v,
      by_cases h : x = y,
        begin
          rewrite h at ht_t,
          cases ht_t,
          have ht' : has_type (partial_map.update y T' $
                              partial_map.update y U gamma)
                             t
                             ht_t_T₁₂,
          from ht_t_a,
          rewrite partial_map.update_shadow at ht',
          simp [h, subst],
          exact t_abs ht',
        end,
        begin
          cases ht_t,
          have ht' : has_type (partial_map.update y T' $
                               partial_map.update x U gamma)
                              t
                              ht_t_T₁₂,
          from ht_t_a,
          rewrite partial_map.update_permute (ne.symm h) at ht',
          simp [h, subst],
          exact t_abs (ih ht' ht_v),
        end,
    },
    case tm.app: _ _ ih₁ ih₂ {
      intros _ _ ht_t ht_v,
      cases ht_t,
      simp [subst],
      exact t_app (ih₁ ht_t_a ht_v) (ih₂ ht_t_a_1 ht_v),
    },
    case tm.tru: { intros _ _ ht_t _, cases ht_t, simp [subst], exact t_tru },
    case tm.fls: { intros _ _ ht_t _, cases ht_t, simp [subst], exact t_fls },
    case tm.tst: t₁ t₂ t₃ ih₁ ih₂ ih₃ {
      intros _ _ ht_t ht_v,
      cases ht_t,
      simp [subst],
      exact t_tst (ih₁ ht_t_a ht_v) (ih₂ ht_t_a_1 ht_v) (ih₃ ht_t_a_2 ht_v),
    },
end

theorem preservation {t T} :
  has_type context.empty t T -> ∀{t'}, (t -+> t') -> has_type context.empty t' T :=
begin
  generalize h : context.empty = gamma,
  intro ht,
  induction ht,
    case has_type.t_var: { intros _ s, cases s },
    case has_type.t_abs: { intros _ s, cases s },
    case has_type.t_app: _ _ _ _ _ ht₁ ht₂ ih₁ ih₂  {
      intros _ s,
      cases s,
        case step.st_appabs: {
          rewrite <-h at ht₁,
          cases ht₁,
          rewrite <-h at ht₂,
          simp [symm h],
          exact substitution_preserves_typing ht₁_a ht₂,
        },
        case step.st_app1: { exact t_app (ih₁ h s_a) ht₂ },
        case step.st_app2: { exact t_app ht₁ (ih₂ h s_a_1) },
    },
    case has_type.t_tru: { intros _ s, cases s },
    case has_type.t_fls: { intros _ s, cases s },
    case has_type.t_tst: _ _ _ _ _ ht₁ ht₂ ht₃ ih₁ ih₂ ih₃ {
      intros _ s,
      cases s,
        case step.st_tsttru: { exact ht₂ },
        case step.st_tstfls: { exact ht₃ },
        case step.st_tst: { exact t_tst (ih₁ h s_a) ht₂ ht₃ },
    },
end

lemma subject_expansion :
  ∃t t' T,
  (t -+> t') -> has_type context.empty t' T -> ¬has_type context.empty t T :=
begin
  existsi tru,
  existsi fls,
  existsi ty.bool,
  intro s,
  cases s,
end

lemma soundness {t t' T} (ht : has_type context.empty t T) (ss : t -+>* t') :
  ¬stuck t' :=
begin
  intros stck,
  induction ss,
    case multi.multi_refl: {
      rcases stck with ⟨nf,  nv⟩,
      rcases progress ht with v | st,
        { exact nv v },
        { exact nf st },
    },
    case multi.multi_step: _ _ _ s _ ih { exact ih (preservation ht s) stck },
end
