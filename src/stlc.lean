import .logic .maps

@[derive decidable_eq]
inductive ty : Type
| bool : ty
| arrow : ty -> ty -> ty
| nat : ty
| prod : ty -> ty -> ty
| unit : ty
| sum : ty -> ty -> ty
| list : ty -> ty

open ty

inductive tm : Type
| var : string -> tm
| abs : string -> ty -> tm -> tm
| app : tm -> tm -> tm
| const : ℕ -> tm
| prd : tm -> tm
| scc : tm -> tm
| mlt : tm -> tm -> tm
| iszro : tm -> tm
| tru : tm
| fls : tm
| tst : tm -> tm -> tm -> tm
| let_ : string -> tm -> tm -> tm
| pair : tm -> tm -> tm
| fst : tm -> tm
| snd : tm -> tm
| unit : tm
| inl : ty -> tm -> tm
| inr : ty -> tm -> tm
| scase : tm -> string -> tm -> string -> tm -> tm
| nil : ty -> tm
| cons : tm -> tm -> tm
| lcase : tm -> tm -> string -> string -> tm -> tm
| fix : tm -> tm

open tm

def idB := abs "x" bool (var "x")
def idBB := abs "x" (arrow bool bool) (var "x")
def idBBBB := abs "x" (arrow (arrow bool bool) (arrow bool bool)) (var "x")
def k := abs "x" bool (abs "y" bool (var "x"))
def notB := abs "x" bool (tst (var "x") fls tru)

inductive value : tm -> Prop
| v_abs {x T t} : value (abs x T t)
| v_const {n} : value (const n)
| v_tru : value tru
| v_fls : value fls
| v_pair {t₁ t₂} : value t₁ -> value t₂ -> value (pair t₁ t₂)
| v_unit : value unit
| v_inl {t T} : value t -> value (inl T t)
| v_inr {t T} : value t -> value (inr T t)
| v_nil {T} : value (nil T)
| v_cons {t₁ t₂} : value t₁ -> value t₂ -> value (cons t₁ t₂)

open value

def subst (x : string) (s : tm) : tm -> tm
| (var y) := if x = y then s else var y
| (abs y T t1) := abs y T (if x = y then t1 else subst t1)
| (app t1 t2) := app (subst t1) (subst t2)
| (const n) := const n
| (prd t) := prd (subst t)
| (scc t) := scc (subst t)
| (mlt t₁ t₂) := mlt (subst t₁) (subst t₂)
| (iszro t) := iszro (subst t)
| tru := tru
| fls := fls
| (tst t1 t2 t3) := tst (subst t1) (subst t2) (subst t3)
| (let_ y t₁ t₂) := let_ y (subst t₁) (if x = y then t₂ else (subst t₂))
| (pair t₁ t₂) := pair (subst t₁) (subst t₂)
| (fst t) := fst (subst t)
| (snd t) := snd (subst t)
| unit := unit
| (inl T t) := inl T (subst t)
| (inr T t) := inr T (subst t)
| (scase t y t₁ z t₂) := scase (subst t)
                               y (if x = y then t₁ else (subst t₁))
                               z (if x = z then t₂ else (subst t₂))
| (nil T) := nil T
| (cons t₁ t₂) := cons (subst t₁) (subst t₂)
| (lcase t t₁ y z t₂) := lcase (subst t)
                               (subst t₁)
                               y z (if x = y ∨ x = z then t₂ else subst t₂)
| (fix t) := fix (subst t)

notation `[` x `:=` s `]` t := subst x s t

inductive substi (s : tm) (x : string) : tm -> tm -> Prop
| s_var1 : substi (var x) s
| s_var2 {y : string} : y ≠ x -> substi (var y) (var y)
| s_abs1 {T : ty} {t : tm} : substi (abs x T t) (abs x T t)
| s_abs2 {y : string} {T : ty} {t t' : tm} :
    y ≠ x -> substi t t' -> substi (abs y T t) (abs y T t')
| s_app {t1 t1' t2 t2' : tm} :
    substi t1 t1' -> substi t2 t2' -> substi (app t1 t2) (app t1' t2')
| s_const {n} : substi (const n) (const n)
| s_prd {t t'} : substi t t' -> substi (prd t) (prd t')
| s_scc {t t'} : substi t t' -> substi (scc t) (scc t')
| s_mlt {t₁ t₁' t₂ t₂'} :
    substi t₁ t₁' -> substi t₂ t₂' -> substi (mlt t₁ t₂) (mlt t₁' t₂')
| s_iszro {t t'} : substi t t' -> substi (iszro t) (iszro t')
| s_tru : substi tru tru
| s_fls : substi fls fls
| s_tst {t1 t1' t2 t2' t3 t3' : tm} :
    substi t1 t1' -> substi t2 t2' -> substi t3 t3' ->
    substi (tst t1 t2 t3) (tst t1' t2' t3')
| s_let1 {t₁ t₁' t₂} : substi t₁ t₁' -> substi (let_ x t₁ t₂) (let_ x t₁' t₂)
| s_let2 {y t₁ t₁' t₂ t₂'} :
    y ≠ x ->
    substi t₁ t₁' ->
    substi t₂ t₂' ->
    substi (let_ y t₁ t₂) (let_ y t₁' t₂')
| s_pair {t₁ t₁' t₂ t₂' } :
    substi t₁ t₁' -> substi t₂ t₂' -> substi (pair t₁ t₂) (pair t₁' t₂')
| s_fst {t t'} : substi t t' -> substi (fst t) (fst t')
| s_snd {t t'} : substi t t' -> substi (snd t) (snd t')
| s_unit : substi unit unit
| s_inl {t t' T} : substi t t' -> substi (inl T t) (inl T t')
| s_inr {t t' T} : substi t t' -> substi (inr T t) (inr T t')
| s_scase1 {t t' t₁ t₂} :
    substi t t' -> substi (scase t x t₁ x t₂) (scase t' x t₁ x t₂)
| s_scase2 {y t t' t₁ t₁' t₂} :
    y ≠ x ->
    substi t t' ->
    substi t₁ t₁' ->
    substi (scase t y t₁ x t₂) (scase t' y t₁' x t₂)
| s_scase3 {z t t' t₁ t₂ t₂'} :
    z ≠ x ->
    substi t t' ->
    substi t₂ t₂' ->
    substi (scase t x t₁ z t₂) (scase t' x t₁ z t₂')
| s_scase4 {y z t t' t₁ t₁' t₂ t₂'} :
    y ≠ x ->
    z ≠ x ->
    substi t t' ->
    substi t₁ t₁' ->
    substi t₂ t₂' ->
    substi (scase t y t₁ z t₂) (scase t' y t₁' z t₂')
| s_nil {T} : substi (nil T) (nil T)
| s_cons {t₁ t₁' t₂ t₂'} :
    substi t₁ t₁' -> substi t₂ t₂' -> substi (cons t₁ t₂) (cons t₁' t₂')
| s_lcase1 {t t' t₁ t₁' t₂} :
    substi t t' ->
    substi t₁ t₁' ->
    substi (lcase t t₁ x x t₂) (lcase t' t₁' x x t₂)
| s_lcase2 {t t' t₁ t₁' y t₂} :
    y ≠ x ->
    substi t t' ->
    substi t₁ t₁' ->
    substi (lcase t t₁ y x t₂) (lcase t' t₁' y x t₂)
| s_lcase3 {t t' t₁ t₁' z t₂} :
    z ≠ x ->
    substi t t' ->
    substi t₁ t₁' ->
    substi (lcase t t₁ x z t₂) (lcase t' t₁' x z t₂)
| s_lcase4 {t t' t₁ t₁' y z t₂ t₂'} :
    y ≠ x ->
    z ≠ x ->
    substi t t' ->
    substi t₁ t₁' ->
    substi t₂ t₂' ->
    substi (lcase t t₁ y z t₂) (lcase t' t₁' y z t₂')
| s_fix {t t'} : substi t t' -> substi (fix t) (fix t')

theorem substi_correct : ∀ x s t t', ([x:=s]t) = t' ↔ substi s x t t' :=
begin
  intros,
  apply iff.intro,
  { intro prf,
    induction prf,
    induction t,
      case tm.var: y {
        unfold subst,
        by_cases h : x = y,
          { simp [*], apply substi.s_var1 },
          { simp [*], apply substi.s_var2, exact ne.symm h },
      },
      case tm.app: { apply substi.s_app, repeat { assumption } },
      case tm.abs: y {
        unfold subst,
        by_cases h : x = y,
          { simp [*], apply substi.s_abs1 },
          { simp [*], apply substi.s_abs2, exact ne.symm h, assumption, },
      },
      case tm.const: { apply substi.s_const },
      case tm.prd: { apply substi.s_prd, assumption },
      case tm.scc: { apply substi.s_scc, assumption },
      case tm.iszro: { apply substi.s_iszro, assumption },
      case tm.mlt: { apply substi.s_mlt, repeat { assumption } },
      case tm.tru: { apply substi.s_tru },
      case tm.fls: { apply substi.s_fls },
      case tm.tst: { apply substi.s_tst, repeat { assumption } },
      case tm.let_: y _ _ ih₁ ih₂ {
        unfold subst,
        by_cases h : x = y,
          { simp [h], rewrite h at ih₁, exact substi.s_let1 ih₁ },
          { simp [h], exact substi.s_let2 (ne.symm h) ih₁ ih₂, },
      },
      case tm.pair: { apply substi.s_pair, repeat { assumption } },
      case tm.fst: { apply substi.s_fst, assumption },
      case tm.snd: { apply substi.s_snd, assumption },
      case tm.unit: { apply substi.s_unit },
      case tm.inl: { apply substi.s_inl, assumption },
      case tm.inr: { apply substi.s_inr, assumption },
      case tm.scase: _ y _ z _ ih ih₁ ih₂ {
        unfold subst,
        by_cases hxy : x = y,
          { by_cases hxz : x = z,
              { simp [hxy, hxz, eq.trans (symm hxz) hxy],
                rewrite hxy at ih,
                exact substi.s_scase1 ih },
              { simp [hxy, hxz],
                rewrite hxy at hxz,
                rewrite hxy at ih,
                rewrite hxy at ih₂,
                exact substi.s_scase3 (ne.symm hxz) ih ih₂ } },
          { by_cases hxz : x = z,
              { simp [hxy, hxz],
                rewrite hxz at hxy,
                rewrite hxz at ih,
                rewrite hxz at ih₁,
                exact substi.s_scase2 (ne.symm hxy) ih ih₁ },
              { simp [hxy, hxz],
                exact
                  substi.s_scase4 (ne.symm hxy) (ne.symm hxz) ih ih₁ ih₂ } },
      },
      case tm.nil: { apply substi.s_nil },
      case tm.cons: { apply substi.s_cons, repeat { assumption } },
      case tm.lcase: _ _ y z _ ih ih₁ ih₂ {
        unfold subst,
        by_cases hxy : x = y,
          { by_cases hxz : x = z,
              { simp [*],
                rewrite <-hxy,
                rewrite <-hxz,
                exact substi.s_lcase1 ih ih₁ },
              { simp [*],
                rewrite <-hxy,
                exact substi.s_lcase3 (ne.symm hxz) ih ih₁ } },
          { by_cases hxz : x = z,
              { simp [*],
                rewrite <-hxz,
                exact substi.s_lcase2 (ne.symm hxy) ih ih₁ },
              { simp [*],
                exact substi.s_lcase4 (ne.symm hxy) (ne.symm hxz) ih ih₁ ih₂ } }
      },
      case tm.fix: _ ih { exact substi.s_fix ih } },
  { intro sub,
    induction sub,
    repeat { simp [*, subst]; simp [ne.symm sub_a]; simp [ne.symm sub_a_1] } },
end

inductive step : tm -> tm -> Prop
| st_appabs {x T t12 v2} : value v2 -> step (app (abs x T t12) v2) ([x:=v2]t12)
| st_app1 {t1 t1' t2} : step t1 t1' -> step (app t1 t2) (app t1' t2)
| st_app2 {v1 t2 t2'} : value v1 -> step t2 t2' -> step (app v1 t2) (app v1 t2')
| st_prdzro : step (prd (const 0)) (const 0)
| st_prdnzr {n} : step (prd (const (nat.succ n))) (const n)
| st_prd {t t'} : step t t' -> step (prd t) (prd t')
| st_sccn {n} : step (scc (const n)) (const (nat.succ n))
| st_scc {t t'} : step t t' -> step (scc t) (scc t')
| st_mlt1 {t₁ t₁' t₂} : step t₁ t₁' -> step (mlt t₁ t₂) (mlt t₁' t₂)
| st_mlt2 {t₁ t₂ t₂'} :
    value t₁ -> step t₂ t₂' -> step (mlt t₁ t₂) (mlt t₁ t₂')
| st_mltnm {n m} : step (mlt (const n) (const m)) (const (n * m))
| st_iszrozro : step (iszro (const 0)) tru
| st_iszronzr {n} : step (iszro (const (nat.succ n))) fls
| st_iszro {t t'} : step t t' -> step (iszro t) (iszro t')
| st_tsttru {t2 t3} : step (tst tru t2 t3) t2
| st_tstfls {t2 t3} : step (tst fls t2 t3) t3
| st_tst {t₁ t₁' t₂ t₃} : step t₁ t₁' -> step (tst t₁ t₂ t₃) (tst t₁' t₂ t₃)
| st_let {t₁ t₁' x t₂} : step t₁ t₁' -> step (let_ x t₁ t₂) (let_ x t₁' t₂)
| st_letvalue {x t₁ t₂} : value t₁ -> step (let_ x t₁ t₂) ([x:=t₁]t₂)
| st_pair1 {t₁ t₁' t₂} : step t₁ t₁' -> step (pair t₁ t₂) (pair t₁' t₂)
| st_pair2 {t₁ t₂ t₂'} :
    value t₁ -> step t₂ t₂' -> step (pair t₁ t₂) (pair t₁ t₂')
| st_fstpair {t₁ t₂} : value t₁ -> value t₂ -> step (fst (pair t₁ t₂)) t₁
| st_fst {t t'} : step t t' -> step (fst t) (fst t')
| st_sndpair {t₁ t₂} : value t₁ -> value t₂ -> step (snd (pair t₁ t₂)) t₂
| st_snd {t t'} : step t t' -> step (snd t) (snd t')
| st_inl {t t' T} : step t t' -> step (inl T t) (inl T t')
| st_inr {t t' T} : step t t' -> step (inr T t) (inr T t')
| st_scase {t t' y t₁ z t₂} :
    step t t' -> step (scase t y t₁ z t₂) (scase t' y t₁ z t₂)
| st_scaseinl {T t y t₁ z t₂} :
    value t -> step (scase (inl T t) y t₁ z t₂) ([y:=t]t₁)
| st_scaseinr {T t y t₁ z t₂} :
    value t -> step (scase (inr T t) y t₁ z t₂) ([z:=t]t₂)
| st_cons1 {t₁ t₁' t₂} : step t₁ t₁' -> step (cons t₁ t₂) (cons t₁' t₂)
| st_cons2 {t₁ t₂ t₂'} :
    value t₁ -> step t₂ t₂' -> step (cons t₁ t₂) (cons t₁ t₂')
| st_lcase {t t' t₁ y z t₂} :
    step t t' -> step (lcase t t₁ y z t₂) (lcase t' t₁ y z t₂)
| st_lcasenil {T t₁ y z t₂} : step (lcase (nil T) t₁ y z t₂) t₁
| st_lcasecons {t_h t_t t₁ y z t₂} :
    value t_h ->
    value t_t ->
    step (lcase (cons t_h t_t) t₁ y z t₂) ([y:=t_h][z:=t_t]t₂)
| st_fix {t t'} : step t t' -> step (fix t) (fix t')
| st_fixabs {x T t} : step (fix (abs x T t)) ([x:=fix (abs x T t)]t)

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
| t_const {gamma n} : has_type gamma (const n) nat
| t_prd {gamma t} : has_type gamma t nat -> has_type gamma (prd t) nat
| t_scc {gamma t} : has_type gamma t nat -> has_type gamma (scc t) nat
| t_mlt {gamma t₁ t₂} :
    has_type gamma t₁ nat ->
    has_type gamma t₂ nat ->
    has_type gamma (mlt t₁ t₂) nat
| t_iszro {gamma t} : has_type gamma t nat -> has_type gamma (iszro t) bool
| t_tru {gamma} : has_type gamma tru bool
| t_fls {gamma} : has_type gamma fls bool
| t_tst {gamma T t₁ t₂ t₃} :
    has_type gamma t₁ bool ->
    has_type gamma t₂ T ->
    has_type gamma t₃ T ->
    has_type gamma (tst t₁ t₂ t₃) T
| t_let {gamma x T₁ T₂ t₁ t₂} :
    has_type gamma t₁ T₁ ->
    has_type (partial_map.update x T₁ gamma) t₂ T₂ ->
    has_type gamma (let_ x t₁ t₂) T₂
| t_pair {gamma t₁ T₁ t₂ T₂} :
    has_type gamma t₁ T₁ ->
    has_type gamma t₂ T₂ ->
    has_type gamma (pair t₁ t₂) (prod T₁ T₂)
| t_fst {gamma t T₁ T₂} :
    has_type gamma t (prod T₁ T₂) -> has_type gamma (fst t) T₁
| t_snd {gamma t T₁ T₂} :
    has_type gamma t (prod T₁ T₂) -> has_type gamma (snd t) T₂
| t_unit {gamma} : has_type gamma unit unit
| t_inl {gamma t T₁ T₂} :
    has_type gamma t T₁ -> has_type gamma (inl T₂ t) (sum T₁ T₂)
| t_inr {gamma t T₂ T₁} :
    has_type gamma t T₂ -> has_type gamma (inr T₁ t) (sum T₁ T₂)
| t_scase {gamma t T₁ T₂ y t₁ T z t₂} :
    has_type gamma t (sum T₁ T₂) ->
    has_type (partial_map.update y T₁ gamma) t₁ T ->
    has_type (partial_map.update z T₂ gamma) t₂ T ->
    has_type gamma (scase t y t₁ z t₂) T
| t_nil {gamma T} : has_type gamma (nil T) (list T)
| t_cons {gamma t₁ t₂ T} :
    has_type gamma t₁ T ->
    has_type gamma t₂ (list T) ->
    has_type gamma (cons t₁ t₂) (list T)
| t_lcase {gamma t T t₁ T' y z t₂} :
    has_type gamma t (list T) ->
    has_type gamma t₁ T' ->
    has_type (partial_map.update z (list T) $ partial_map.update y T gamma)
             t₂
             T' ->
    has_type gamma (lcase t t₁ y z t₂) T'
| t_fix {gamma t T} : has_type gamma t (arrow T T) -> has_type gamma (fix t) T

open has_type

example : has_type context.empty (abs "x" bool (var "x")) (arrow bool bool) :=
t_abs (t_var rfl)

meta def auto_typing : tactic unit :=
tactic.repeat (   tactic.applyc ``t_tru
              <|> tactic.applyc ``t_fls
              <|> tactic.applyc ``t_const
              <|> (tactic.applyc ``t_var >> tactic.reflexivity)
              <|> tactic.applyc ``t_abs
              <|> tactic.applyc ``t_prd
              <|> tactic.applyc ``t_scc
              <|> tactic.applyc ``t_iszro
              <|> tactic.applyc ``t_tst
              <|> tactic.applyc ``t_let )

example : has_type context.empty (abs "x" bool (var "x")) (arrow bool bool) :=
by auto_typing

example {t : ty} : has_type context.empty
                            (abs "x" t
                              (abs "y" (arrow t t)
                                (app (var "y") (app (var "y") (var "x")))))
                            (arrow t (arrow (arrow t t) t)) :=
t_abs (t_abs (t_app (t_var rfl) (t_app (t_var rfl) (t_var rfl))))

example : ∃t, has_type context.empty
                       (abs "x" (arrow bool bool)
                         (abs "y" (arrow bool bool)
                           (abs "z" bool
                             (app (var "y") (app (var "x") (var "z"))))))
                       t :=
⟨ arrow (arrow bool bool)
        (arrow (arrow bool bool)
               (arrow bool bool))
, t_abs (t_abs (t_abs (t_app (t_var rfl) (t_app (t_var rfl) (t_var rfl))))) ⟩

lemma arrow_no_confusion {t₁ t₂} : arrow t₁ t₂ ≠ t₁ :=
assume h : arrow t₁ t₂ = t₁,
begin
  induction t₁,
    case ty.arrow: _ _ ih₁ ih₂ {
      apply ih₁,
      injection h with h' h'',
      rewrite h'',
      exact h',
    },
    /- ty.bool, ty.nat -/
    repeat { cases h },
end

example : ¬∃s t, has_type context.empty (abs "x" s (app (var "x") (var "x"))) t :=
assume ⟨ _, _, t_abs (t_app (t_var h₁) (t_var h₂)) ⟩,
have h : some (arrow _ _) = some _, from eq.trans (eq.symm h₁) h₂,
option.no_confusion h (assume h', arrow_no_confusion h')

inductive appears_free_in (x : string) : tm -> Prop
| afi_var : appears_free_in (var x)
| afi_abs {y t T} : y ≠ x -> appears_free_in t -> appears_free_in (abs y T t)
| afi_app1 {t₁ t₂} : appears_free_in t₁ -> appears_free_in (app t₁ t₂)
| afi_app2 {t₁ t₂} : appears_free_in t₂ -> appears_free_in (app t₁ t₂)
| afi_prd {t} : appears_free_in t -> appears_free_in (prd t)
| afi_scc {t} : appears_free_in t -> appears_free_in (scc t)
| afi_mlt1 {t₁ t₂} : appears_free_in t₁ -> appears_free_in (mlt t₁ t₂)
| afi_mlt2 {t₁ t₂} : appears_free_in t₂ -> appears_free_in (mlt t₁ t₂)
| afi_iszro {t} : appears_free_in t -> appears_free_in (iszro t)
| afi_tst1 {t₁ t₂ t₃} : appears_free_in t₁ -> appears_free_in (tst t₁ t₂ t₃)
| afi_tst2 {t₁ t₂ t₃} : appears_free_in t₂ -> appears_free_in (tst t₁ t₂ t₃)
| afi_tst3 {t₁ t₂ t₃} : appears_free_in t₃ -> appears_free_in (tst t₁ t₂ t₃)
| afi_let1 {y t₁ t₂} : appears_free_in t₁ -> appears_free_in (let_ y t₁ t₂)
| afi_let2 {y t₁ t₂} :
    y ≠ x -> appears_free_in t₂ -> appears_free_in (let_ y t₁ t₂)
| afi_pair1 {t₁ t₂} : appears_free_in t₁ -> appears_free_in (pair t₁ t₂)
| afi_pair2 {t₁ t₂} : appears_free_in t₂ -> appears_free_in (pair t₁ t₂)
| afi_fst {t} : appears_free_in t -> appears_free_in (fst t)
| afi_snd {t} : appears_free_in t -> appears_free_in (snd t)
| afi_inl {t T} : appears_free_in t -> appears_free_in (inl T t)
| afi_inr {t T} : appears_free_in t -> appears_free_in (inr T t)
| afi_scase1 {t y t₁ z t₂} :
    appears_free_in t -> appears_free_in (scase t y t₁ z t₂)
| afi_scase2 {t y t₁ z t₂} :
    y ≠ x -> appears_free_in t₁ -> appears_free_in (scase t y t₁ z t₂)
| afi_scase3 {t y t₁ z t₂} :
    z ≠ x -> appears_free_in t₂ -> appears_free_in (scase t y t₁ z t₂)
| afi_cons1 {t₁ t₂} : appears_free_in t₁ -> appears_free_in (cons t₁ t₂)
| afi_cons2 {t₁ t₂} : appears_free_in t₂ -> appears_free_in (cons t₁ t₂)
| afi_lcase1 {t t₁ y z t₂} :
    appears_free_in t -> appears_free_in (lcase t t₁ y z t₂)
| afi_lcase2 {t t₁ y z t₂} :
    appears_free_in t₁ -> appears_free_in (lcase t t₁ y z t₂)
| afi_lcase3 {t t₁ y z t₂} :
    y ≠ x -> z ≠ x -> appears_free_in t₂ -> appears_free_in (lcase t t₁ y z t₂)
| afi_fix {t} : appears_free_in t -> appears_free_in (fix t)

def closed (t : tm) := ∀x, ¬appears_free_in x t

def stuck (t : tm) := normal_form step t ∧ ¬value t

def num_test : tm :=
tst (iszro (prd (scc (prd (mlt (const 2) (const 0))))))
  (const 5)
  (const 6)

example : has_type context.empty num_test nat :=
t_tst (t_iszro (t_prd (t_scc (t_prd (t_mlt t_const t_const))))) t_const t_const

example : num_test -+>* const 5 :=
multi_step (st_tst (st_iszro (st_prd (st_scc (st_prd st_mltnm))))) $
multi_step (st_tst (st_iszro (st_prd (st_scc st_prdzro)))) $
multi_step (st_tst (st_iszro (st_prd st_sccn))) $
multi_step (st_tst (st_iszro st_prdnzr)) $
multi_step (st_tst st_iszrozro) $
multi_step st_tsttru $
multi_refl

def prod_test : tm :=
snd (fst (pair (pair (const 5) (const 6)) (const 7)))

example : has_type context.empty prod_test nat :=
t_snd (t_fst (t_pair (t_pair t_const t_const) t_const))

example : prod_test -+>* const 6 :=
multi_step (st_snd (st_fstpair (v_pair v_const v_const) v_const)) $
multi_step (st_sndpair v_const v_const) $
multi_refl

def let_test : tm :=
let_ "x" (prd (const 6))
  (scc (var "x"))

example : has_type context.empty let_test nat :=
t_let (t_prd t_const) (t_scc (t_var rfl))

example : let_test -+>* const 6 :=
multi_step (st_let st_prdnzr) $
multi_step (st_letvalue v_const) $
multi_step st_sccn $
multi_refl

def sum_test_1 : tm :=
scase (inl nat (const 5))
  "x" (var "x")
  "y" (var "y")

example : has_type context.empty sum_test_1 nat :=
t_scase (t_inl t_const) (t_var rfl) (t_var rfl)

example : sum_test_1 -+>* const 5 :=
multi_step (st_scaseinl v_const) $
multi_refl

def sum_test_2 : tm :=
let_ "processSum" (abs "x" (sum nat nat)
                    (scase (var "x")
                      "n" (var "n")
                      "n" (tst (iszro (var "n")) (const 1) (const 0))))
  (pair (app (var "processSum") (inl nat (const 5)))
        (app (var "processSum") (inr nat (const 5))))

example : has_type context.empty sum_test_2 (prod nat nat) :=
t_let (t_abs (t_scase (t_var rfl)
                      (t_var rfl)
                      (t_tst (t_iszro (t_var rfl)) t_const t_const)))
  (t_pair (t_app (t_var rfl) (t_inl t_const))
          (t_app (t_var rfl) (t_inr t_const)))

example : sum_test_2 -+>* pair (const 5) (const 0) :=
multi_step (st_letvalue v_abs) $
multi_step (st_pair1 (st_appabs (v_inl v_const))) $
multi_step (st_pair1 (st_scaseinl v_const)) $
multi_step (st_pair2 v_const (st_appabs (v_inr v_const))) $
multi_step (st_pair2 v_const (st_scaseinr v_const)) $
multi_step (st_pair2 v_const (st_tst st_iszronzr)) $
multi_step (st_pair2 v_const st_tstfls) $
multi_refl

def list_test : tm :=
let_ "l" (cons (const 5) (cons (const 6) (nil nat)))
  (lcase (var "l")
    (const 0)
    "x" "y" (mlt (var "x") (var "x")))

example : has_type context.empty list_test nat :=
t_let (t_cons t_const (t_cons t_const t_nil))
      (t_lcase (t_var rfl) t_const (t_mlt (t_var rfl) (t_var rfl)))

example : list_test -+>* const 25 :=
multi_step (st_letvalue (v_cons v_const (v_cons v_const v_nil))) $
multi_step (st_lcasecons v_const (v_cons v_const v_nil)) $
multi_step st_mltnm $
multi_refl

def fix_fact : tm :=
fix (abs "f" (arrow nat nat)
      (abs "a" nat
        (tst (iszro (var "a"))
          (const 1)
          (mlt (var "a") (app (var "f") (prd (var "a")))))))

example : has_type context.empty fix_fact (arrow nat nat) :=
t_fix (t_abs (t_abs (t_tst (t_iszro (t_var rfl))
                           t_const
                           (t_mlt (t_var rfl)
                                  (t_app (t_var rfl) (t_prd (t_var rfl)))))))

example : app fix_fact (const 4) -+>* const 24 :=
multi_step (st_app1 st_fixabs) $
multi_step (st_appabs v_const) $
multi_step (st_tst st_iszronzr) $
multi_step st_tstfls $
multi_step (st_mlt2 v_const (st_app1 st_fixabs)) $
multi_step (st_mlt2 v_const (st_app2 v_abs st_prdnzr)) $
multi_step (st_mlt2 v_const (st_appabs v_const)) $
multi_step (st_mlt2 v_const (st_tst st_iszronzr)) $
multi_step (st_mlt2 v_const st_tstfls) $
multi_step (st_mlt2 v_const (st_mlt2 v_const (st_app1 st_fixabs))) $
multi_step (st_mlt2 v_const (st_mlt2 v_const (st_app2 v_abs st_prdnzr))) $
multi_step (st_mlt2 v_const (st_mlt2 v_const (st_appabs v_const))) $
multi_step (st_mlt2 v_const (st_mlt2 v_const (st_tst st_iszronzr))) $
multi_step (st_mlt2 v_const (st_mlt2 v_const st_tstfls)) $
multi_step (st_mlt2
             v_const
             (st_mlt2 v_const (st_mlt2 v_const (st_app1 st_fixabs)))) $
multi_step (st_mlt2
             v_const
             (st_mlt2 v_const (st_mlt2 v_const (st_app2 v_abs st_prdnzr)))) $
multi_step (st_mlt2
             v_const
             (st_mlt2 v_const (st_mlt2 v_const (st_appabs v_const)))) $
multi_step (st_mlt2
             v_const
             (st_mlt2 v_const (st_mlt2 v_const (st_tst st_iszronzr)))) $
multi_step (st_mlt2
             v_const
             (st_mlt2 v_const (st_mlt2 v_const st_tstfls))) $
multi_step (st_mlt2
             v_const
             (st_mlt2
               v_const
               (st_mlt2 v_const (st_mlt2 v_const (st_app1 st_fixabs))))) $
multi_step (st_mlt2
             v_const
             (st_mlt2
               v_const
               (st_mlt2 v_const (st_mlt2 v_const (st_app2 v_abs st_prdnzr))))) $
multi_step (st_mlt2
             v_const
             (st_mlt2
               v_const
               (st_mlt2 v_const (st_mlt2 v_const (st_appabs v_const))))) $
multi_step (st_mlt2
             v_const
             (st_mlt2
               v_const
               (st_mlt2 v_const (st_mlt2 v_const (st_tst st_iszrozro))))) $
multi_step (st_mlt2
             v_const
             (st_mlt2 v_const (st_mlt2 v_const (st_mlt2 v_const st_tsttru)))) $
multi_step (st_mlt2 v_const (st_mlt2 v_const (st_mlt2 v_const st_mltnm))) $
multi_step (st_mlt2 v_const (st_mlt2 v_const st_mltnm)) $
multi_step (st_mlt2 v_const st_mltnm) $
multi_step st_mltnm $
multi_refl

def fix_map : tm :=
abs "g" (arrow nat nat)
  (fix (abs "f" (arrow (list nat) (list nat))
         (abs "l" (list nat)
           (lcase (var "l")
             (nil nat)
             "a" "l" (cons (app (var "g") (var "a"))
                           (app (var "f") (var "l")))))))

example : has_type context.empty
                   fix_map
                   (arrow (arrow nat nat) (arrow (list nat) (list nat))) :=
t_abs (t_fix (t_abs (t_abs (t_lcase (t_var rfl)
                                    t_nil
                                    (t_cons (t_app (t_var rfl) (t_var rfl))
                                            (t_app (t_var rfl) (t_var rfl)))))))

example :    app (app fix_map (abs "a" nat (scc (var "a"))))
                 (cons (const 1) (cons (const 2) (nil nat)))
        -+>* cons (const 2) (cons (const 3) (nil nat)) :=
multi_step (st_app1 (st_appabs v_abs)) $
multi_step (st_app1 st_fixabs) $
multi_step (st_appabs (v_cons v_const (v_cons v_const v_nil))) $
multi_step (st_lcasecons v_const (v_cons v_const v_nil)) $
multi_step (st_cons1 (st_appabs v_const)) $
multi_step (st_cons1 st_sccn) $
multi_step (st_cons2 v_const (st_app1 st_fixabs)) $
multi_step (st_cons2 v_const (st_appabs (v_cons v_const v_nil))) $
multi_step (st_cons2 v_const (st_lcasecons v_const v_nil)) $
multi_step (st_cons2 v_const (st_cons1 (st_appabs v_const))) $
multi_step (st_cons2 v_const (st_cons1 st_sccn)) $
multi_step (st_cons2 v_const (st_cons2 v_const (st_app1 st_fixabs))) $
multi_step (st_cons2 v_const (st_cons2 v_const (st_appabs v_nil))) $
multi_step (st_cons2 v_const (st_cons2 v_const st_lcasenil)) $
multi_refl

def fix_equal : tm :=
fix (abs "eq" (arrow nat (arrow nat nat))
      (abs "m" nat
        (abs "n" nat
          (tst (iszro (var "m"))
            (tst (iszro (var "n")) (const 1) (const 0))
            (tst (iszro (var "n"))
              (const 0)
              (app (app (var "eq") (prd (var "m")))
                   (prd (var "n"))))))))

example : has_type context.empty fix_equal (arrow nat (arrow nat nat)) :=
t_fix (t_abs (t_abs (t_abs (t_tst (t_iszro (t_var rfl))
                             (t_tst (t_iszro (t_var rfl)) t_const t_const)
                             (t_tst (t_iszro (t_var rfl))
                               t_const
                               (t_app (t_app (t_var rfl) (t_prd (t_var rfl)))
                                      (t_prd (t_var rfl))))))))

example : app (app fix_equal (const 4)) (const 4) -+>* const 1 :=
multi_step (st_app1 (st_app1 st_fixabs)) $
multi_step (st_app1 (st_appabs v_const)) $
multi_step (st_appabs v_const) $
multi_step (st_tst st_iszronzr) $
multi_step st_tstfls $
multi_step (st_tst st_iszronzr) $
multi_step st_tstfls $
multi_step (st_app1 (st_app1 st_fixabs)) $
multi_step (st_app1 (st_app2 v_abs st_prdnzr)) $
multi_step (st_app1 (st_appabs v_const)) $
multi_step (st_app2 v_abs st_prdnzr) $
multi_step (st_appabs v_const) $
multi_step (st_tst st_iszronzr) $
multi_step st_tstfls $
multi_step (st_tst st_iszronzr) $
multi_step st_tstfls $
multi_step (st_app1 (st_app1 st_fixabs)) $
multi_step (st_app1 (st_app2 v_abs st_prdnzr)) $
multi_step (st_app1 (st_appabs v_const)) $
multi_step (st_app2 v_abs st_prdnzr) $
multi_step (st_appabs v_const) $
multi_step (st_tst st_iszronzr) $
multi_step st_tstfls $
multi_step (st_tst st_iszronzr) $
multi_step st_tstfls $
multi_step (st_app1 (st_app1 st_fixabs)) $
multi_step (st_app1 (st_app2 v_abs st_prdnzr)) $
multi_step (st_app1 (st_appabs v_const)) $
multi_step (st_app2 v_abs st_prdnzr) $
multi_step (st_appabs v_const) $
multi_step (st_tst st_iszronzr) $
multi_step st_tstfls $
multi_step (st_tst st_iszronzr) $
multi_step st_tstfls $
multi_step (st_app1 (st_app1 st_fixabs)) $
multi_step (st_app1 (st_app2 v_abs st_prdnzr)) $
multi_step (st_app1 (st_appabs v_const)) $
multi_step (st_app2 v_abs st_prdnzr) $
multi_step (st_appabs v_const) $
multi_step (st_tst st_iszrozro) $
multi_step st_tsttru $
multi_step (st_tst st_iszrozro) $
multi_step st_tsttru $
multi_refl

example : app (app fix_equal (const 4)) (const 5) -+>* const 0 :=
multi_step (st_app1 (st_app1 st_fixabs)) $
multi_step (st_app1 (st_appabs v_const)) $
multi_step (st_appabs v_const) $
multi_step (st_tst st_iszronzr) $
multi_step st_tstfls $
multi_step (st_tst st_iszronzr) $
multi_step st_tstfls $
multi_step (st_app1 (st_app1 st_fixabs)) $
multi_step (st_app1 (st_app2 v_abs st_prdnzr)) $
multi_step (st_app1 (st_appabs v_const)) $
multi_step (st_app2 v_abs st_prdnzr) $
multi_step (st_appabs v_const) $
multi_step (st_tst st_iszronzr) $
multi_step st_tstfls $
multi_step (st_tst st_iszronzr) $
multi_step st_tstfls $
multi_step (st_app1 (st_app1 st_fixabs)) $
multi_step (st_app1 (st_app2 v_abs st_prdnzr)) $
multi_step (st_app1 (st_appabs v_const)) $
multi_step (st_app2 v_abs st_prdnzr) $
multi_step (st_appabs v_const) $
multi_step (st_tst st_iszronzr) $
multi_step st_tstfls $
multi_step (st_tst st_iszronzr) $
multi_step st_tstfls $
multi_step (st_app1 (st_app1 st_fixabs)) $
multi_step (st_app1 (st_app2 v_abs st_prdnzr)) $
multi_step (st_app1 (st_appabs v_const)) $
multi_step (st_app2 v_abs st_prdnzr) $
multi_step (st_appabs v_const) $
multi_step (st_tst st_iszronzr) $
multi_step st_tstfls $
multi_step (st_tst st_iszronzr) $
multi_step st_tstfls $
multi_step (st_app1 (st_app1 st_fixabs)) $
multi_step (st_app1 (st_app2 v_abs st_prdnzr)) $
multi_step (st_app1 (st_appabs v_const)) $
multi_step (st_app2 v_abs st_prdnzr) $
multi_step (st_appabs v_const) $
multi_step (st_tst st_iszrozro) $
multi_step st_tsttru $
multi_step (st_tst st_iszronzr) $
multi_step st_tstfls $
multi_refl

def evenodd : tm :=
let_ "evenodd" (fix (abs "eo" (prod (arrow nat nat) (arrow nat nat))
                      (pair (abs "n" nat
                              (tst (iszro (var "n"))
                                (const 1)
                                (app (snd (var "eo")) (prd (var "n")))))
                            (abs "n" nat
                              (tst (iszro (var "n"))
                                (const 0)
                                (app (fst (var "eo")) (prd (var "n"))))))))
  (let_ "even" (fst (var "evenodd"))
    (let_ "odd" (snd (var "evenodd"))
      (pair (app (var "even") (const 3))
            (app (var "even") (const 4)))))

example : has_type context.empty evenodd (prod nat nat) :=
t_let (t_fix
        (t_abs
          (t_pair (t_abs (t_tst (t_iszro (t_var rfl))
                           t_const
                           (t_app (t_snd (t_var rfl)) (t_prd (t_var rfl)))))
                  (t_abs (t_tst (t_iszro (t_var rfl))
                           t_const
                           (t_app (t_fst (t_var rfl)) (t_prd (t_var rfl))))))))
  (t_let (t_fst (t_var rfl))
    (t_let (t_snd (t_var rfl))
      (t_pair (t_app (t_var rfl) t_const)
              (t_app (t_var rfl) t_const))))

example : evenodd -+>* pair (const 0) (const 1) :=
multi_step (st_let st_fixabs) $
multi_step (st_letvalue (v_pair v_abs v_abs)) $
multi_step (st_let (st_fstpair v_abs v_abs)) $
multi_step (st_letvalue v_abs) $
multi_step (st_let (st_sndpair v_abs v_abs)) $
multi_step (st_letvalue v_abs) $
multi_step (st_pair1 (st_appabs v_const)) $
multi_step (st_pair1 (st_tst st_iszronzr)) $
multi_step (st_pair1 st_tstfls) $
multi_step (st_pair1 (st_app1 (st_snd st_fixabs))) $
multi_step (st_pair1 (st_app1 (st_sndpair v_abs v_abs))) $
multi_step (st_pair1 (st_app2 v_abs st_prdnzr)) $
multi_step (st_pair1 (st_appabs v_const)) $
multi_step (st_pair1 (st_tst st_iszronzr)) $
multi_step (st_pair1 st_tstfls) $
multi_step (st_pair1 (st_app1 (st_fst st_fixabs))) $
multi_step (st_pair1 (st_app1 (st_fstpair v_abs v_abs))) $
multi_step (st_pair1 (st_app2 v_abs st_prdnzr)) $
multi_step (st_pair1 (st_appabs v_const)) $
multi_step (st_pair1 (st_tst st_iszronzr)) $
multi_step (st_pair1 st_tstfls) $
multi_step (st_pair1 (st_app1 (st_snd st_fixabs))) $
multi_step (st_pair1 (st_app1 (st_sndpair v_abs v_abs))) $
multi_step (st_pair1 (st_app2 v_abs st_prdnzr)) $
multi_step (st_pair1 (st_appabs v_const)) $
multi_step (st_pair1 (st_tst st_iszrozro)) $
multi_step (st_pair1 st_tsttru) $
multi_step (st_pair2 v_const (st_appabs v_const)) $
multi_step (st_pair2 v_const (st_tst st_iszronzr)) $
multi_step (st_pair2 v_const st_tstfls) $
multi_step (st_pair2 v_const (st_app1 (st_snd st_fixabs))) $
multi_step (st_pair2 v_const (st_app1 (st_sndpair v_abs v_abs))) $
multi_step (st_pair2 v_const (st_app2 v_abs st_prdnzr)) $
multi_step (st_pair2 v_const (st_appabs v_const)) $
multi_step (st_pair2 v_const (st_tst st_iszronzr)) $
multi_step (st_pair2 v_const st_tstfls) $
multi_step (st_pair2 v_const (st_app1 (st_fst st_fixabs))) $
multi_step (st_pair2 v_const (st_app1 (st_fstpair v_abs v_abs))) $
multi_step (st_pair2 v_const (st_app2 v_abs st_prdnzr)) $
multi_step (st_pair2 v_const (st_appabs v_const)) $
multi_step (st_pair2 v_const (st_tst st_iszronzr)) $
multi_step (st_pair2 v_const st_tstfls) $
multi_step (st_pair2 v_const (st_app1 (st_snd st_fixabs))) $
multi_step (st_pair2 v_const (st_app1 (st_sndpair v_abs v_abs))) $
multi_step (st_pair2 v_const (st_app2 v_abs st_prdnzr)) $
multi_step (st_pair2 v_const (st_appabs v_const)) $
multi_step (st_pair2 v_const (st_tst st_iszronzr)) $
multi_step (st_pair2 v_const st_tstfls) $
multi_step (st_pair2 v_const (st_app1 (st_fst st_fixabs))) $
multi_step (st_pair2 v_const (st_app1 (st_fstpair v_abs v_abs))) $
multi_step (st_pair2 v_const (st_app2 v_abs st_prdnzr)) $
multi_step (st_pair2 v_const (st_appabs v_const)) $
multi_step (st_pair2 v_const (st_tst st_iszrozro)) $
multi_step (st_pair2 v_const st_tsttru) $
multi_refl
