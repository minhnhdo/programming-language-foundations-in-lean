import tactic
import .stlc

lemma cannonical_forms_bool {t}
  (ht : has_type context.empty t ty.bool) (v : value t) :
  t = tm.tru ∨ t = tm.fls :=
begin
  cases v,
    case value.v_tru: { left, constructor },
    case value.v_fls: { right, constructor },
    repeat { cases ht },
end

lemma cannonical_forms_fun {t T₁ T₂}
  (ht : has_type context.empty t (ty.arrow T₁ T₂)) (v : value t) :
  ∃x u, t = tm.abs x T₁ u :=
begin
  cases v,
    case value.v_abs : { cases ht, existsi _, existsi _, reflexivity },
    repeat { cases ht },
end

lemma cannonical_forms_nat {t}
  (ht : has_type context.empty t ty.nat) (v : value t) :
  ∃n, t = tm.const n :=
begin
  cases v,
    case value.v_const: { existsi _, reflexivity },
    repeat { cases ht },
end

lemma cannonical_forms_pair {t T₁ T₂}
  (ht : has_type context.empty t (ty.prod T₁ T₂)) (v : value t) :
  ∃t₁ t₂, t = tm.pair t₁ t₂ :=
begin
  cases v,
    case value.v_pair: { existsi _, existsi _, reflexivity },
    repeat { cases ht },
end

lemma cannonical_forms_unit {t}
  (ht : has_type context.empty t ty.unit) (v : value t) :
  t = tm.unit :=
begin
  cases v,
    case value.v_unit: { reflexivity },
    repeat { cases ht },
end

lemma cannonical_forms_sum {t T₁ T₂}
  (ht : has_type context.empty t (ty.sum T₁ T₂)) (v : value t) :
  (∃t₁, t = tm.inl T₂ t₁) ∨ (∃t₂, t = tm.inr T₁ t₂) :=
begin
  cases v,
    case value.v_inl: { cases ht, left, existsi _, reflexivity },
    case value.v_inr: { cases ht, right, existsi _, reflexivity },
    repeat { cases ht },
end

lemma cannonical_forms_list {t T}
  (ht : has_type context.empty t (ty.list T)) (v : value t) :
  (t = tm.nil T ∨ ∃t₁ t₂, value t₁ ∧ value t₂ ∧ t = tm.cons t₁ t₂) :=
begin
  cases v,
    case value.v_nil: { cases ht, left, constructor },
    case value.v_cons: _ _ v₁ v₂ {
      cases ht,
      right,
      existsi _,
      existsi _,
      split,
      exact v₁,
      split,
      exact v₂,
      reflexivity,
    },
    repeat { cases ht },
end

theorem progress {t T} :
  has_type context.empty t T -> value t ∨ ∃t', t -+> t' :=
begin
  generalize h : context.empty = e,
  intro ht,
  induction ht,
    case has_type.t_var: _ _ _ ht { rewrite <-h at ht, cases ht },
    case has_type.t_app: _ _ _ _ _ ht₁ _ ih₁ ih₂ {
      rcases ih₁ h with v₁ | ⟨_, s₁⟩,
        { rcases ih₂ h with v₂ | ⟨_, s₂⟩,
            { cases v₁; cases ht₁, right, existsi _, exact step.st_appabs v₂ },
            { right, existsi _, exact step.st_app2 v₁ s₂ } },
        { right, existsi _, exact step.st_app1 s₁ },
    },
    case has_type.t_prd: _ _ ht ih {
      rcases ih h with v | ⟨_, s⟩,
        { rewrite <-h at ht,
          rcases cannonical_forms_nat ht v with ⟨n, h'⟩,
          rewrite h',
          right,
          cases n with m,
            { existsi _, exact step.st_prdzro },
            { existsi _, exact step.st_prdnzr } },
        { right, existsi _, exact step.st_prd s },
    },
    case has_type.t_scc: _ _ ht ih {
      rcases ih h with v | ⟨_, s⟩,
        { rewrite <-h at ht,
          rcases cannonical_forms_nat ht v with ⟨_, h'⟩,
          rewrite h',
          right,
          existsi _,
          exact step.st_sccn },
        { right, existsi _, exact step.st_scc s },
    },
    case has_type.t_mlt: _ _ _ ht₁ ht₂ ih₁ ih₂ {
      rcases ih₁ h with v₁ | ⟨_, s₁⟩,
        { rewrite <-h at ht₁,
          rcases cannonical_forms_nat ht₁ v₁ with ⟨_, h₁⟩,
          rewrite h₁ at v₁,
          rewrite h₁,
          rcases ih₂ h with v₂ | ⟨_, s₂⟩,
            { rewrite <-h at ht₂,
              rcases cannonical_forms_nat ht₂ v₂ with ⟨_, h₂⟩,
              rewrite h₂,
              right,
              existsi _,
              exact step.st_mltnm },
            { right, existsi _, exact step.st_mlt2 v₁ s₂ },
        },
        { right, existsi _, exact step.st_mlt1 s₁ },
    },
    case has_type.t_iszro: _ _ ht ih {
      rcases ih h with v | ⟨_, s⟩,
        { rewrite <-h at ht,
          rcases cannonical_forms_nat ht v with ⟨n, h'⟩,
          rewrite h',
          right,
          cases n with m,
            { existsi _, exact step.st_iszrozro },
            { existsi _, exact step.st_iszronzr } },
        { right, existsi _, exact step.st_iszro s },
    },
    case has_type.t_tst: _ _ _ _ _ ht₁ _ _ ih₁ {
      rcases ih₁ h with v₁ | ⟨_, s₁⟩,
        { rewrite <-h at ht₁,
          cases cannonical_forms_bool ht₁ v₁,
          repeat { simp [*], right, existsi _ },
            { exact step.st_tsttru },
            { exact step.st_tstfls }, },
        { right, existsi _, exact step.st_tst s₁ },
    },
    case has_type.t_let: _ _ _ _ _ _ _ _ ih₁ ih₂ {
      rcases ih₁ h with v₁ | ⟨_, s₁⟩,
        { right, existsi _, exact step.st_letvalue v₁ },
        { right, existsi _, exact step.st_let s₁ },
    },
    case has_type.t_pair: _ _ _ _ _ _ _ ih₁ ih₂ {
      rcases ih₁ h with v₁ | ⟨_, s₁⟩,
        { rcases ih₂ h with v₂ | ⟨_, s₂⟩,
            { left, exact value.v_pair v₁ v₂ },
            { right, existsi _, exact step.st_pair2 v₁ s₂ } },
        { right, existsi _, exact step.st_pair1 s₁ },
    },
    case has_type.t_fst: _ _ _ _ ht ih {
      rcases ih h with v | ⟨_, s⟩,
        { rewrite <-h at ht,
          rcases cannonical_forms_pair ht v with ⟨_, _, h'⟩,
          rewrite h',
          right,
          existsi _,
          exact step.st_fstpair },
        { right, existsi _, exact step.st_fst s },
    },
    case has_type.t_snd: _ _ _ _ ht ih {
      rcases ih h with v | ⟨_, s⟩,
        { rewrite <-h at ht,
          rcases cannonical_forms_pair ht v with ⟨_, _, h'⟩,
          rewrite h',
          right,
          existsi _,
          exact step.st_sndpair },
        { right, existsi _, exact step.st_snd s },
    },
    case has_type.t_inl: _ _ _ _ ht ih {
      rcases ih h with v | ⟨_, s⟩,
        { left, exact value.v_inl v },
        { right, existsi _, exact step.st_inl s },
    },
    case has_type.t_inr: _ _ _ _ ht ih {
      rcases ih h with v | ⟨_, s⟩,
        { left, exact value.v_inr v },
        { right, existsi _, exact step.st_inr s }
    },
    case has_type.t_scase: _ _ _ _ _ _ _ _ _ ht _ _ ih {
      rcases ih h with v | ⟨_, s⟩,
        { rewrite <-h at ht,
          rcases cannonical_forms_sum ht v with ⟨_, h_inl⟩ | ⟨_, h_inr⟩,
            { rewrite h_inl, right, existsi _, exact step.st_scaseinl },
            { rewrite h_inr, right, existsi _, exact step.st_scaseinr } },
        { right, existsi _, exact step.st_scase s },
    },
    case has_type.t_cons: _ _ _ _ _ _ ih₁ ih₂ {
      rcases ih₁ h with v₁ | ⟨_, s₁⟩,
        { rcases ih₂ h with v₂ | ⟨_, s₂⟩,
            { left, exact value.v_cons v₁ v₂ },
            { right, existsi _, exact step.st_cons2 v₁ s₂ } },
        { right, existsi _, exact step.st_cons1 s₁ },
    },
    case has_type.t_lcase: _ _ _ _ _ _ _ _ ht _ _ ih {
      rcases ih h with v | ⟨_, s⟩,
        { rewrite <-h at ht,
          rcases cannonical_forms_list ht v
            with h_nil | ⟨_, _, v_h, v_t, h_cons⟩,
              { rewrite h_nil, right, existsi _, exact step.st_lcasenil },
              { rewrite h_cons,
                right,
                existsi _,
                exact step.st_lcasecons v_h v_t } },
        { right, existsi _, exact step.st_lcase s },
    },
    repeat { left, constructor },
end

theorem progress' :
  ∀{t T}, has_type context.empty t T -> value t ∨ ∃t', t -+> t' :=
begin
  intro t,
  induction t,
    case tm.var: { intros _ ht, cases ht, cases ht_a },
    case tm.app: _ _ ih₁ ih₂ {
      intros _ ht,
      cases ht,
      rcases ih₁ ht_a with v₁ | ⟨_, s₁⟩,
        { rcases ih₂ ht_a_1 with v₂ | ⟨_, s₂⟩,
            { rcases cannonical_forms_fun ht_a v₁ with ⟨_, _, h⟩,
              rewrite h,
              right,
              existsi _,
              exact step.st_appabs v₂ },
            { right, existsi _, exact step.st_app2 v₁ s₂ } },
        { right, existsi _, exact step.st_app1 s₁ },
    },
    case tm.prd: _ ih {
      intros _ ht,
      cases ht,
      rcases ih ht_a with v | ⟨_, s⟩,
        { rcases cannonical_forms_nat ht_a v with ⟨n, h⟩,
          right,
          rewrite h,
          cases n with m,
            { existsi _, exact step.st_prdzro },
            { existsi _, exact step.st_prdnzr } },
        { right, existsi _, exact step.st_prd s },
    },
    case tm.scc: _ ih {
      intros _ ht,
      cases ht,
      rcases ih ht_a with v | ⟨_, s⟩,
        { rcases cannonical_forms_nat ht_a v with ⟨_, h⟩,
          right,
          rewrite h,
          existsi _,
          exact step.st_sccn },
        { right, existsi _, exact step.st_scc s },
    },
    case tm.mlt: _ _ ih₁ ih₂ {
      intros _ ht,
      cases ht,
      rcases ih₁ ht_a with v₁ | ⟨_, s₁⟩,
        { rcases cannonical_forms_nat ht_a v₁ with ⟨_, h₁⟩,
          right,
          rewrite h₁ at v₁,
          rewrite h₁,
          rcases ih₂ ht_a_1 with v₂ | ⟨_, s₂⟩,
            { rcases cannonical_forms_nat ht_a_1 v₂ with ⟨_, h₂⟩,
              rewrite h₂,
              existsi _,
              exact step.st_mltnm },
            { existsi _, exact step.st_mlt2 v₁ s₂ } },
        { right, existsi _, exact step.st_mlt1 s₁ },
    },
    case tm.iszro: _ ih {
      intros _ ht,
      cases ht,
      rcases ih ht_a with v | ⟨_, s⟩,
        { rcases cannonical_forms_nat ht_a v with ⟨n, h⟩,
          right,
          rewrite h,
          cases n with m,
            { existsi _, exact step.st_iszrozro },
            { existsi _, exact step.st_iszronzr } },
        { right, existsi _, exact step.st_iszro s },
    },
    case tm.tst: _ _ _ ih₁ ih₂ ih₃ {
      intros _ ht,
      cases ht,
      rcases ih₁ ht_a with v₁ | ⟨_, s₁⟩,
        { cases cannonical_forms_bool ht_a v₁ with h_tru h_fls,
            { rewrite h_tru, right, existsi _, exact step.st_tsttru },
            { rewrite h_fls, right, existsi _, exact step.st_tstfls } },
        { right, existsi _, exact step.st_tst s₁ },
    },
    case tm.let_: _ _ _ ih₁ ih₂ {
      intros _ ht,
      cases ht,
      rcases ih₁ ht_a with v₁ | ⟨_, s₁⟩,
        { right, existsi _, exact step.st_letvalue v₁ },
        { right, existsi _, exact step.st_let s₁ },
    },
    case tm.pair: _ _ ih₁ ih₂ {
      intros _ ht,
      cases ht,
      rcases ih₁ ht_a with v₁ | ⟨_, s₁⟩,
        { rcases ih₂ ht_a_1 with v₂ | ⟨_, s₂⟩,
            { left, exact value.v_pair v₁ v₂ },
            { right, existsi _, exact step.st_pair2 v₁ s₂ } },
        { right, existsi _, exact step.st_pair1 s₁ },
    },
    case tm.fst: _ ih {
      intros _ ht,
      cases ht,
      rcases ih ht_a with v | ⟨_, s⟩,
        { rcases cannonical_forms_pair ht_a v with ⟨_, _, h'⟩,
          rewrite h',
          right,
          existsi _,
          exact step.st_fstpair },
        { right, existsi _, exact step.st_fst s },
    },
    case tm.snd: _ ih {
      intros _ ht,
      cases ht,
      rcases ih ht_a with v | ⟨_, s⟩,
        { rcases cannonical_forms_pair ht_a v with ⟨_, _, h'⟩,
          rewrite h',
          right,
          existsi _,
          exact step.st_sndpair },
        { right, existsi _, exact step.st_snd s },
    },
    case tm.inl: _ _ ih {
      intros _ ht,
      cases ht,
      rcases ih ht_a with v | ⟨_, s⟩,
        { left, exact value.v_inl v },
        { right, existsi _, exact step.st_inl s },
    },
    case tm.inr: _ _ ih {
      intros _ ht,
      cases ht,
      rcases ih ht_a with v | ⟨_, s⟩,
        { left, exact value.v_inr v },
        { right, existsi _, exact step.st_inr s },
    },
    case tm.scase: _ _ _ _ _ ih ih₁ ih₂ {
      intros _ ht,
      cases ht,
      rcases ih ht_a with v | ⟨_, s⟩,
        { rcases cannonical_forms_sum ht_a v with ⟨_, h_inl⟩ | ⟨_, h_inr⟩,
            { rewrite h_inl, right, existsi _, exact step.st_scaseinl },
            { rewrite h_inr, right, existsi _, exact step.st_scaseinr },
          },
        { right, existsi _, exact step.st_scase s },
    },
    case tm.cons: _ _ ih₁ ih₂ {
      intros _ ht,
      cases ht,
      rcases ih₁ ht_a with v₁ | ⟨_, s₁⟩,
        { rcases ih₂ ht_a_1 with v₂ | ⟨_, s₂⟩,
            { left, exact value.v_cons v₁ v₂ },
            { right, existsi _, exact step.st_cons2 v₁ s₂ } },
        { right, existsi _, exact step.st_cons1 s₁ },
    },
    case tm.lcase: _ _ _ _ _ ih ih₁ ih₂ {
      intros _ ht,
      cases ht,
      rcases ih ht_a with v | ⟨_, s⟩,
        { rcases cannonical_forms_list ht_a v
            with h_nil | ⟨_, _, v_h, v_t, h_cons⟩,
              { rewrite h_nil, right, existsi _, exact step.st_lcasenil },
              { rewrite h_cons,
                right,
                existsi _,
                exact step.st_lcasecons v_h v_t } },
        { right, existsi _, exact step.st_lcase s },
    },
    repeat { intros, left, constructor },
end

lemma free_in_context {x t} (afi : appears_free_in x t) :
  ∀{gamma T}, has_type gamma t T -> ∃T', gamma x = some T' :=
begin
  induction afi,
    repeat { intros, cases a },
    /- appears_free_in.afi_var -/ { existsi T, assumption },
    /- appears_free_in.afi_abs -/ {
      rcases afi_ih a_a with ⟨T', h'⟩,
      rewrite partial_map.update_neq afi_a at h',
      existsi T',
      exact h',
    },
    repeat { apply afi_ih, assumption },
    /- appears_free_in.afi_let2 -/ {
      rcases afi_ih a_a_1 with ⟨T', h'⟩,
      rewrite partial_map.update_neq afi_a at h',
      existsi T',
      exact h',
    },
    /- appears_free_in.afi_scase2 -/ {
      let e := afi_ih a_a_1,
      rewrite partial_map.update_neq afi_a at e,
      exact e,
    },
    /- appears_free_in.afi_scase3 -/ {
      let e := afi_ih a_a_2,
      rewrite partial_map.update_neq afi_a at e,
      exact e,
    },
    /- appears_free_in.afi_lcase3 -/ {
      let e := afi_ih a_a_2,
      rewrite [partial_map.update_neq afi_a_1, partial_map.update_neq afi_a]
        at e,
      exact e,
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
      apply has_type.t_var,
      rewrite <-f (appears_free_in.afi_var x),
      exact h,
    },
    case has_type.t_abs: _ x T₁ _ _ _ ih {
      intros gamma' f,
      apply has_type.t_abs,
      apply @ih (partial_map.update x T₁ gamma'),
      intros y afi,
      by_cases h : x = y,
        repeat {
          simp [h, partial_map.update, total_map.update];
          exact f (appears_free_in.afi_abs h afi)
        },
    },
    case has_type.t_app: _ _ _ _ _ _ _ ih₁ ih₂ {
      intros _ f,
      apply has_type.t_app,
      repeat { apply ih₁ <|> apply ih₂, intros x afi, apply @f x },
        { exact appears_free_in.afi_app1 afi },
        { exact appears_free_in.afi_app2 afi },
    },
    case has_type.t_tst: gamma _ _ _ _ _ _ _ ih₁ ih₂ ih₃ {
      intros _ f,
      apply has_type.t_tst,
      repeat {
        apply ih₁ <|> apply ih₂ <|> apply ih₃,
        intros x afi,
        apply @f x
      },
        { exact appears_free_in.afi_tst1 afi },
        { exact appears_free_in.afi_tst2 afi },
        { exact appears_free_in.afi_tst3 afi },
    },
    case has_type.t_prd: _ _ _ ih {
      intros _ f,
      apply has_type.t_prd,
      apply ih,
      intros x afi,
      apply @f x,
      exact appears_free_in.afi_prd afi,
    },
    case has_type.t_scc: _ _ _ ih {
      intros _ f,
      apply has_type.t_scc,
      apply ih,
      intros x afi,
      apply @f x,
      exact appears_free_in.afi_scc afi,
    },
    case has_type.t_mlt: _ _ _ _ _ ih₁ ih₂ {
      intros _ f,
      apply has_type.t_mlt,
      repeat { apply ih₁ <|> apply ih₂, intros x afi, apply @f x },
        { exact appears_free_in.afi_mlt1 afi },
        { exact appears_free_in.afi_mlt2 afi },
    },
    case has_type.t_iszro: _ _ _ ih {
      intros _ f,
      apply has_type.t_iszro,
      apply ih,
      intros x afi,
      apply @f x,
      exact appears_free_in.afi_iszro afi,
    },
    case has_type.t_let: _ x _ _ _ _ _ _ ih₁ ih₂ {
      intros _ f,
      apply has_type.t_let,
        { apply ih₁,
          intros y afi,
          apply @f y, exact appears_free_in.afi_let1 afi },
        { apply ih₂,
          intros y afi,
          by_cases h : x = y,
          repeat { simp [*, partial_map.update, total_map.update] },
          apply @f y,
          exact appears_free_in.afi_let2 h afi },
    },
    case has_type.t_pair: _ _ _ _ _ _ _ ih₁ ih₂ {
      intros _ f,
      apply has_type.t_pair,
        { apply ih₁,
          intros _ afi,
          exact f (appears_free_in.afi_pair1 afi) },
        { apply ih₂,
          intros y afi,
          exact f (appears_free_in.afi_pair2 afi) },
    },
    case has_type.t_fst: _ _ _ _ _ ih {
      intros _ f,
      apply has_type.t_fst,
      apply ih,
      intros _ afi,
      exact f (appears_free_in.afi_fst afi),
    },
    case has_type.t_snd: _ _ _ _ _ ih {
      intros _ f,
      apply has_type.t_snd,
      apply ih,
      intros _ afi,
      exact f (appears_free_in.afi_snd afi),
    },
    case has_type.t_inl: _ _ _ _ _ ih {
      intros _ f,
      apply has_type.t_inl,
      apply ih,
      intros _ afi,
      exact f (appears_free_in.afi_inl afi),
    },
    case has_type.t_inr: _ _ _ _ _ ih {
      intros _ f,
      apply has_type.t_inr,
      apply ih,
      intros _ afi,
      exact f (appears_free_in.afi_inr afi),
    },
    case has_type.t_scase: _ _ _ _ y _ _ z _ _ _ _ ih ih₁ ih₂ {
      intros _ f,
      apply has_type.t_scase,
        { apply ih,
          intros _ afi,
          exact f (appears_free_in.afi_scase1 afi) },
        { apply ih₁,
          intros _ afi,
          by_cases h : y = x,
            { simp [h, partial_map.update, total_map.update], },
            { simp [h, partial_map.update, total_map.update],
              exact f (appears_free_in.afi_scase2 h afi) } },
        { apply ih₂,
          intros _ afi,
          by_cases h : z = x,
            { simp [h, partial_map.update, total_map.update] },
            { simp [h, partial_map.update, total_map.update],
              exact f (appears_free_in.afi_scase3 h afi) } },
    },
    case has_type.t_cons: _ _ _ _ _ _ ih₁ ih₂ {
      intros _ f,
      apply has_type.t_cons,
        { apply ih₁,
          intros _ afi,
          exact f (appears_free_in.afi_cons1 afi) },
        { apply ih₂,
          intros _ afi,
          exact f (appears_free_in.afi_cons2 afi) },
    },
    case has_type.t_lcase: _ _ T _ _ y z _ _ _ _ ih ih₁ ih₂ {
      intros _ f,
      apply has_type.t_lcase,
        { apply ih,
          intros _ afi,
          exact f (appears_free_in.afi_lcase1 afi) },
        { apply ih₁,
          intros _ afi,
          exact f (appears_free_in.afi_lcase2 afi) },
        { apply ih₂,
          intros _ afi,
          by_cases hyx : y = x,
            { simp [symm hyx, partial_map.update, total_map.update] },
            { by_cases hzx : z = x,
                { simp [symm hzx, partial_map.update, total_map.update] },
                { simp [hyx, hzx, partial_map.update, total_map.update],
                  exact f (appears_free_in.afi_lcase3 hyx hzx afi) } } },
    },
    repeat {
      intros,
          exact has_type.t_const
      <|> exact has_type.t_tru
      <|> exact has_type.t_fls
      <|> exact has_type.t_unit
      <|> exact has_type.t_nil
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
      repeat {
        try { rewrite h at ht_t },
        cases ht_t,
        simp [h] at ht_t_a,
        simp [h, ht_t_a, subst],
      },
        { rewrite ht_t_a at ht_v,
          apply context_invariance ht_v,
          intros z afi,
          apply false.elim,
          exact typable_empty__closed ht_v z afi },
        { exact has_type.t_var ht_t_a },
    },
    case tm.abs: y T' t ih {
      intros T gamma ht_t ht_v,
      by_cases h : x = y,
        { rewrite h at ht_t,
          cases ht_t,
          have ht' : has_type (partial_map.update y T' $
                              partial_map.update y U gamma)
                             t
                             ht_t_T₁₂,
          from ht_t_a,
          rewrite partial_map.update_shadow at ht',
          simp [h, subst],
          exact has_type.t_abs ht' },
        { cases ht_t,
          have ht' : has_type (partial_map.update y T' $
                               partial_map.update x U gamma)
                              t
                              ht_t_T₁₂,
          from ht_t_a,
          rewrite partial_map.update_permute (ne.symm h) at ht',
          simp [h, subst],
          exact has_type.t_abs (ih ht' ht_v) },
    },
    case tm.app: _ _ ih₁ ih₂ {
      intros _ _ ht_t ht_v,
      cases ht_t,
      exact has_type.t_app (ih₁ ht_t_a ht_v) (ih₂ ht_t_a_1 ht_v),
    },
    case tm.prd: _ ih {
      intros _ _ ht_t ht_v,
      cases ht_t,
      exact has_type.t_prd (ih ht_t_a ht_v),
    },
    case tm.scc: _ ih {
      intros _ _ ht_t ht_v,
      cases ht_t,
      exact has_type.t_scc (ih ht_t_a ht_v),
    },
    case tm.mlt: _ _ ih₁ ih₂ {
      intros _ _ ht_t ht_v,
      cases ht_t,
      exact has_type.t_mlt (ih₁ ht_t_a ht_v) (ih₂ ht_t_a_1 ht_v),
    },
    case tm.iszro: _ ih {
      intros _ _ ht_t ht_v,
      cases ht_t,
      exact has_type.t_iszro (ih ht_t_a ht_v),
    },
    case tm.tst: _ _ _ ih₁ ih₂ ih₃ {
      intros _ _ ht_t ht_v,
      cases ht_t,
      exact has_type.t_tst (ih₁ ht_t_a ht_v) (ih₂ ht_t_a_1 ht_v) (ih₃ ht_t_a_2 ht_v),
    },
    case tm.let_: y _ _ ih₁ ih₂ {
      intros _ _ ht_t ht_v,
      by_cases h : y = x,
        { cases ht_t,
          simp [h, subst],
          rewrite h at ht_t_a_1,
          have ht₂ : has_type (partial_map.update x ht_t_T₁ $
                               partial_map.update x U gamma)
                              t_a_2
                              T,
          from ht_t_a_1,
          rewrite partial_map.update_shadow at ht₂,
          exact has_type.t_let (ih₁ ht_t_a ht_v) ht₂ },
        { cases ht_t,
          simp [ne.symm h, subst],
          have ht₂ : has_type (partial_map.update y ht_t_T₁ $
                               partial_map.update x U gamma)
                              t_a_2
                              T,
          from ht_t_a_1,
          rewrite partial_map.update_permute h at ht₂,
          exact has_type.t_let (ih₁ ht_t_a ht_v) (ih₂ ht₂ ht_v) },
    },
    case tm.pair: _ _ ih₁ ih₂ {
      intros _ _ ht_t ht_v,
      cases ht_t,
      exact has_type.t_pair (ih₁ ht_t_a ht_v) (ih₂ ht_t_a_1 ht_v),
    },
    case tm.fst: _ ih {
      intros _ _ ht_t ht_v,
      cases ht_t,
      exact has_type.t_fst (ih ht_t_a ht_v),
    },
    case tm.snd: _ ih {
      intros _ _ ht_t ht_v,
      cases ht_t,
      exact has_type.t_snd (ih ht_t_a ht_v),
    },
    case tm.inl: _ _ ih {
      intros _ _ ht_t ht_v,
      cases ht_t,
      exact has_type.t_inl (ih ht_t_a ht_v),
    },
    case tm.inr: _ _ ih {
      intros _ _ ht_t ht_v,
      cases ht_t,
      exact has_type.t_inr (ih ht_t_a ht_v),
    },
    case tm.scase: _ y _ z _ ih ih₁ ih₂{
      intros _ _ ht_t ht_v,
      cases ht_t,
      apply has_type.t_scase (ih ht_t_a ht_v),
        { by_cases h : y = x,
            { simp [h],
              have ht₁ : has_type (partial_map.update y ht_t_T₁ $
                                   partial_map.update x U gamma)
                                  t_a_2
                                  T,
              from ht_t_a_1,
              simp [h, partial_map.update_shadow] at ht₁,
              exact ht₁ },
            { simp [ne.symm h],
              have ht₁ : has_type (partial_map.update y ht_t_T₁ $
                                   partial_map.update x U gamma)
                                  t_a_2
                                  T,
              from ht_t_a_1,
              rewrite partial_map.update_permute h at ht₁,
              exact ih₁ ht₁ ht_v } },
        { by_cases h : z = x,
          { simp [h],
            have ht₂ : has_type (partial_map.update z ht_t_T₂ $
                                 partial_map.update x U gamma)
                                t_a_4
                                T,
            from ht_t_a_2,
            simp [h, partial_map.update_shadow] at ht₂,
            exact ht₂ },
          { simp [ne.symm h],
            have ht₂ : has_type (partial_map.update z ht_t_T₂ $
                                 partial_map.update x U gamma)
                                t_a_4
                                T,
            from ht_t_a_2,
            rewrite partial_map.update_permute h at ht₂,
            exact ih₂ ht₂ ht_v } },
    },
    case tm.cons: _ _ ih₁ ih₂ {
      intros _ _ ht_t ht_v,
      cases ht_t,
      exact has_type.t_cons (ih₁ ht_t_a ht_v) (ih₂ ht_t_a_1 ht_v),
    },
    case tm.lcase: _ _ y z _ ih ih₁ ih₂ {
      intros _ _ ht_t ht_v,
      cases ht_t,
      apply has_type.t_lcase (ih ht_t_a ht_v) (ih₁ ht_t_a_1 ht_v),
      have ht₂ : has_type (partial_map.update z (ty.list ht_t_T) $
                           partial_map.update y ht_t_T $
                           partial_map.update x U gamma)
                          t_a_4
                          T,
      from ht_t_a_2,
      by_cases hyx : y = x,
        { by_cases hzx : z = x,
            { simp [hyx, hzx, partial_map.update_shadow],
              simp [hyx, hzx, partial_map.update_shadow] at ht₂,
              exact ht₂ },
            { simp [ hyx,
                     partial_map.update_permute hzx,
                     partial_map.update_shadow ],
              simp [ hyx,
                     partial_map.update_permute hzx,
                     partial_map.update_shadow ]
                at ht₂,
              exact ht₂ } },
        { by_cases hzx : z = x,
            { simp [hzx],
              simp [ hzx,
                     partial_map.update_permute hyx,
                     partial_map.update_shadow ]
                at ht₂,
              exact ht₂ },
            { let h := iff.elim_right
                         (decidable.not_or_iff_and_not (x = y) (x = z))
                         (and.intro (ne.symm hyx) (ne.symm hzx)),
              simp [h],
              rewrite [ partial_map.update_permute hyx,
                        partial_map.update_permute hzx ]
                at ht₂,
              exact ih₂ ht₂ ht_v } },
    },
    repeat {
      intros _ _ ht_t _,
      cases ht_t,
      simp [subst],
          exact has_type.t_const
      <|> exact has_type.t_tru
      <|> exact has_type.t_fls
      <|> exact has_type.t_unit
      <|> exact has_type.t_nil
    },
end

theorem preservation {t T} :
  has_type context.empty t T -> ∀{t'}, (t -+> t') -> has_type context.empty t' T :=
begin
  generalize h : context.empty = gamma,
  intro ht,
  induction ht,
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
        case step.st_app1: { exact has_type.t_app (ih₁ h s_a) ht₂ },
        case step.st_app2: { exact has_type.t_app ht₁ (ih₂ h s_a_1) },
    },
    case has_type.t_prd: _ _ ht ih {
      intros _ s,
      cases s,
        case step.st_prdzro: { exact ht },
        case step.st_prdnzr: { exact has_type.t_const },
        case step.st_prd: { exact has_type.t_prd (ih h s_a) },
    },
    case has_type.t_scc: _ _ ht ih {
      intros _ s,
      cases s,
        case step.st_sccn: { exact has_type.t_const },
        case step.st_scc: { exact has_type.t_scc (ih h s_a) },
    },
    case has_type.t_mlt: _ _ _ ht₁ ht₂ ih₁ ih₂ {
      intros _ s,
      cases s,
        case step.st_mlt1: { exact has_type.t_mlt (ih₁ h s_a) ht₂ },
        case step.st_mlt2: { exact has_type.t_mlt ht₁ (ih₂ h s_a_1) },
        case step.st_mltnm: { exact has_type.t_const },
    },
    case has_type.t_iszro: _ _ ht ih {
      intros _ s,
      cases s,
        case step.st_iszrozro: { exact has_type.t_tru },
        case step.st_iszronzr: { exact has_type.t_fls },
        case step.st_iszro: { exact has_type.t_iszro (ih h s_a) },
    },
    case has_type.t_tst: _ _ _ _ _ ht₁ ht₂ ht₃ ih₁ ih₂ ih₃ {
      intros _ s,
      cases s,
        case step.st_tsttru: { exact ht₂ },
        case step.st_tstfls: { exact ht₃ },
        case step.st_tst: { exact has_type.t_tst (ih₁ h s_a) ht₂ ht₃ },
    },
    case has_type.t_let: _ _ _ _ _ _ ht₁ ht₂ ih₁ ih₂ {
      intros _ s,
      cases s,
        case step.st_let: { exact has_type.t_let (ih₁ h s_a) ht₂ },
        case step.st_letvalue: {
          rewrite <-h at ht₁,
          exact substitution_preserves_typing ht₂ ht₁,
        },
    },
    case has_type.t_pair: _ _ _ _ _ ht₁ ht₂ ih₁ ih₂ {
      intros _ s,
      cases s,
        case step.st_pair1: { exact has_type.t_pair (ih₁ h s_a) ht₂ },
        case step.st_pair2: { exact has_type.t_pair ht₁ (ih₂ h s_a_1) },
    },
    case has_type.t_fst: _ _ _ _ ht ih {
      intros _ s,
      cases s,
        case step.st_fstpair: { cases ht, exact ht_a, },
        case step.st_fst: { exact has_type.t_fst (ih h s_a) },
    },
    case has_type.t_snd: _ _ _ _ ht ih {
      intros _ s,
      cases s,
        case step.st_sndpair: { cases ht, exact ht_a_1, },
        case step.st_snd: { exact has_type.t_snd (ih h s_a) },
    },
    case has_type.t_inl: _ _ _ _ ht ih {
      intros _ s,
      cases s,
      exact has_type.t_inl (ih h s_a),
    },
    case has_type.t_inr: _ _ _ _ ht ih {
      intros _ s,
      cases s,
      exact has_type.t_inr (ih h s_a),
    },
    case has_type.t_scase: _ _ _ _ y _ _ z _ ht ht₁ ht₂ ih ih₁ ih₂ {
      intros _ s,
      cases s,
        case step.st_scase: { exact has_type.t_scase (ih h s_a) ht₁ ht₂ },
        case step.st_scaseinl: {
          cases ht,
          rewrite <-h at ht_a,
          exact substitution_preserves_typing ht₁ ht_a,
        },
        case step.st_scaseinr: {
          cases ht,
          rewrite <-h at ht_a,
          exact substitution_preserves_typing ht₂ ht_a,
        },
    },
    case has_type.t_cons: _ _ _ _ ht₁ ht₂ ih₁ ih₂ {
      intros _ s,
      cases s,
        { exact has_type.t_cons (ih₁ h s_a) ht₂ },
        { exact has_type.t_cons ht₁ (ih₂ h s_a_1) },
    },
    case has_type.t_lcase: _ _ _ _ _ y z _ ht ht₁ ht₂ ih ih₁ ih₂ {
      intros _ s,
      cases s,
        { exact has_type.t_lcase (ih h s_a) ht₁ ht₂ },
        { exact ht₁ },
        { cases ht,
          rewrite <-h,
          rewrite <-h at ht_a,
          rewrite <-h at ht_a_1,
          rewrite <-h at ht₂,
          exact substitution_preserves_typing
                  (substitution_preserves_typing ht₂ ht_a_1)
                  ht_a },
    },
    repeat { intros _ s, cases s },
end

lemma subject_expansion :
  ∃t t' T,
  (t -+> t') -> has_type context.empty t' T -> ¬has_type context.empty t T :=
begin
  existsi tm.app (tm.abs "x" (ty.arrow ty.bool ty.bool) (tm.var "x")) tm.tru,
  existsi subst "x" tm.tru (tm.var "x"),
  existsi ty.bool,
  intros s ht' ht,
  cases ht,
  cases ht_a,
  cases ht_a_a,
  injection ht_a_a_a with h,
  cases h,
end

lemma soundness {t t' T} (ht : has_type context.empty t T) (ss : t -+>* t') :
  ¬stuck t' :=
begin
  intros stck,
  induction ss,
    case multi.multi_refl: {
      rcases stck with ⟨nf, nv⟩,
      rcases progress ht with v | st,
        { exact nv v },
        { exact nf st },
    },
    case multi.multi_step: _ _ _ s _ ih { exact ih (preservation ht s) stck },
end

theorem unique_types :
  ∀{gamma e T}, has_type gamma e T -> ∀{T'}, has_type gamma e T' -> T = T' :=
begin
  intros _ _ _ ht,
  induction ht,
    case has_type.t_var: _ _ _ h {
      intros _ ht',
      cases ht',
      rewrite h at ht'_a,
      injection ht'_a,
    },
    case has_type.t_abs: _ _ _ _ _ _ ih {
      intros _ ht',
      cases ht',
      apply congr_arg,
      exact ih ht'_a,
    },
    case has_type.t_app: _ _ _ _ _ _ _ ih₁ ih₂ {
      intros _ ht',
      cases ht',
      let h := ih₁ ht'_a,
      rewrite ih₂ ht'_a_1 at h,
      injection h,
    },
    case has_type.t_tst: _ _ _ _ _ _ _ _ _ ih₂ {
      intros _ ht',
      cases ht',
      exact ih₂ ht'_a_1,
    },
    case has_type.t_let: _ _ _ _ _ _ _ _ ih₁ ih₂ {
      intros _ ht',
      cases ht',
      rewrite ih₁ ht'_a at ih₂,
      exact ih₂ ht'_a_1,
    },
    case has_type.t_pair: _ _ _ _ _ _ _ ih₁ ih₂ {
      intros _ ht',
      cases ht',
      rewrite ih₁ ht'_a,
      rewrite ih₂ ht'_a_1,
    },
    case has_type.t_scase: _ _ _ _ _ _ _ _ _ _ _ _ ih ih₁ {
      intros _ ht',
      cases ht',
      cases ih ht'_a,
      exact ih₁ ht'_a_1,
    },
    case has_type.t_cons: _ _ _ _ _ _ _ ih₂ {
      intros _ ht',
      cases ht',
      exact ih₂ ht'_a_1,
    },
    case has_type.t_lcase: _ _ _ _ _ _ _ _ _ _ _ _ ih₁ {
      intros _ ht',
      cases ht',
      exact ih₁ ht'_a_1,
    },
    repeat {
      intros _ ht',
      cases ht',
      cases ht_ih ht'_a,
      reflexivity,
    },
    repeat { intros _ ht', cases ht', reflexivity },
end
