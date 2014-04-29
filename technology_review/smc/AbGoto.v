Require Import
  Coqlib Utf8 String ToString Util
  IntSet
  Containers.Maps
  Integers
  Goto GotoString GotoSem
  LatticeSignatures AdomLib
  AbMachineNonrel.

Set Implicit Arguments.
Unset Elimination Schemes.

Record mem_dom (ab_mem ab_num: Type) :=
{ as_wl:> weak_lattice ab_mem
; var: ab_mem → register → ab_num
; load_single: ab_mem → addr → ab_num
; store_single: ab_mem → addr → ab_num → ab_mem
; assign: ab_mem → register → ab_num → ab_mem
; compare: ab_mem → register → register → ab_mem
; assume: ab_mem → flag → bool → ab_mem+⊥
; init: memory → list addr → ab_mem
}.

Section MEM_DOM_SOUND.
Definition Assign {ab_num: Type} `{ab_machine_int ab_num}
           (E: ℘ machine_config) (rd: register) (v: ab_num) : ℘ machine_config :=
  fun mci => ∃ m, ∃ v',
               E m ∧ γ v v'
             ∧ mci.(mc_flg) = m.(mc_flg)
             ∧ mci.(mc_reg) = m.(mc_reg) # rd ← v'
             ∧ mci.(mc_mem) = m.(mc_mem).

Definition Store {ab_num: Type} `{ab_machine_int ab_num}
           (E: ℘ machine_config) (dst:addr) (v: ab_num) : ℘ machine_config :=
  fun mci => ∃ m v',
               E {| pc := mci.(pc); mc_flg := mci.(mc_flg)
                  ; mc_reg := mci.(mc_reg); mc_mem := m |}
             ∧ v' ∈ γ(v)
             ∧ ∀ a, mci.(mc_mem) a = (m # dst ← v') a.

Definition Compare  {ab_num: Type} `{ab_machine_int ab_num}
           (E: ℘ machine_config) (rs rd: register) : ℘ machine_config :=
  fun mci => ∃ f,
               E {| pc := mci.(pc); mc_flg := f
                  ; mc_reg := mci.(mc_reg); mc_mem := mci.(mc_mem) |}
             ∧ mci.(mc_flg) = eval_flag (mci.(mc_reg) rd) (mci.(mc_reg) rs).

Definition Assume  {ab_num: Type} `{ab_machine_int ab_num}
           (E: ℘ machine_config) (f: flag) (b: bool) : ℘ machine_config :=
  fun mci => E mci ∧ mci.(mc_flg) f = b.

Local Notation "{{ m 'with' 'pc' := pp }}" :=
  ({| pc := pp; mc_flg := m.(mc_flg)
    ; mc_reg := m.(mc_reg); mc_mem := m.(mc_mem) |}).

Let mc_mem' (mc: machine_config) : int → int := mc.(mc_mem).
Local Coercion mc_mem' : machine_config >-> Funclass.

Record mem_dom_sound {ab_mem ab_num} `{ab_machine_int ab_num} (M: mem_dom ab_mem ab_num) (G: gamma_op ab_mem machine_config) : Prop :=
{ as_adom : adom ab_mem machine_config M.(as_wl) G
; var_sound: ∀ ab:ab_mem, ∀ m: machine_config,
      m ∈ γ(ab) → ∀ r, mc_reg m r ∈ γ(M.(var) ab r)
; load_sound: ∀ ab:ab_mem, ∀ m: machine_config,
      m ∈ γ(ab) → ∀ a:addr, m(a) ∈ γ(M.(load_single) ab a)
; assign_sound: ∀ ab:ab_mem, ∀ rd v,
      Assign (γ ab) rd v ⊆ γ(M.(assign) ab rd v)
; store_sound: ∀ ab:ab_mem, ∀ dst v,
      Store (γ ab) dst v ⊆ γ (M.(store_single) ab dst v)
; compare_sound: ∀ ab:ab_mem, ∀ rs rd,
      Compare (γ ab) rs rd ⊆ γ(M.(compare) ab rs rd)
; assume_sound: ∀ ab:ab_mem, ∀ f b,
      Assume (γ ab) f b ⊆ γ(M.(assume) ab f b)
; flow_insensitive: ∀ ab:ab_mem, ∀ m:machine_config,
      m ∈ γ(ab) → ∀ pp, {{ m with pc := pp }} ∈ γ(ab)
; gamma_init: ∀ m:memory, ∀ mci:machine_config, ∀ dom,
      initial_env m (Running mci) → mci ∈ γ(M.(init) m dom)
}.

Context {ab_mem ab_num: Type} `{D: ab_machine_int ab_num} (M: mem_dom ab_mem ab_num).

Definition assume_mem : ab_mem → addr → int → ab_mem := λ ab a val,
  M.(store_single) ab a (const_int val).

Definition AssumeMem (E: ℘ machine_config) (dst: addr) (v: int) : ℘ machine_config :=
  fun mci => ∃ m,
               E {| pc := mci.(pc); mc_flg := mci.(mc_flg)
                  ; mc_reg := mci.(mc_reg); mc_mem := m |}
             ∧ ∀ a, mci.(mc_mem) a = (m # dst ← v) a.

Context (D_correct: ab_machine_int_correct D)
        (G: gamma_op ab_mem machine_config)
        (M_correct: mem_dom_sound M G).

Lemma assume_mem_sound (ab:ab_mem) (a: addr) (val: int) :
    AssumeMem (γ ab) a val ⊆ γ(assume_mem ab a val).
Proof.
  unfold AssumeMem, assume_mem.
  intros [pc f r m'] (m & MEM & ? ). simpl in *.
  apply (store_sound M_correct).
  exists m, val. simpl. intuition;
  apply const_int_correct.
Qed.

End MEM_DOM_SOUND.

Require Generate.
Generate OrderedType register.

Definition value_lt : relation int :=
  fun i j => Int.unsigned i < Int.unsigned j.

Definition value_cmp : int → int → Datatypes.comparison :=
  fun x y => if Int.ltu x y then Lt else if Int.eq x y then Eq else Gt.

Instance OT_ints : OrderedType int := { _eq := eq; _lt := value_lt; _cmp := value_cmp }.
Proof.
  (* strict order *)
  constructor.
  intros x y z; unfold value_lt.
  intros; apply Zlt_trans with (Int.unsigned y); assumption.
  intros x y; unfold value_lt; intros Hlt H.
  rewrite H in Hlt. intuition.
  (* compare_spec *)
  intros x y; unfold value_lt, value_cmp, Int.ltu, Int.eq.
  case_eq (Coqlib.zlt (Int.unsigned x) (Int.unsigned y)).
    intros z H; constructor; assumption.
  case_eq (Coqlib.zeq (Int.unsigned x) (Int.unsigned y)).
    intros e H z H0.
    constructor. unfold Int.unsigned in e.
    destruct x as [x Hx];
    destruct y as [y Hy].
    rewrite (Int.mkint_eq _ _ _ Hy e); reflexivity.
  intros n H z H0.
  constructor.
  intuition.
Defined.

Lemma register_neq_neq : forall u v : register,
  u ≠ v -> u =/= v.
Proof.
intros u v H.
unfold Equivalence.equiv, OrderedType._eq, register_OrderedType.
intros K; destruct K; exact (H eq_refl).
Qed.

Lemma register_eq_eq : forall u v: register, u === v → u = v.
Proof.
  intros u v H.
  destruct (eq_dec u v); auto.
  now refine (False_ind _ (register_neq_neq _ H)).
Qed.

Section AbMachineConfig.

Variable d: Type.
Variable n: ab_machine_int d.
Hypothesis n_correct: ab_machine_int_correct n.

Variable alocs : int_set.

Definition is_aloc (v: addr) : bool :=
  if IntSet.mem (proj v) alocs then true else false.

Lemma is_aloc_cases v :
  ∀ P,
    (IntSet.Mem v alocs → P true) →
    (¬ IntSet.Mem v alocs → P false) →
    P (is_aloc v).
Proof.
  unfold is_aloc, IntSet.Mem.
  intros P. DLib.bif; auto.
Qed.

Record ab_machine_config :=
{ ab_flg: (register * register)+⊤
; ab_reg: Map [ register , d ]
; ab_mem: Map [ int, d ]
}.

(* A key not bound in a map is bound to top *)
Definition find_def {A B} `{OrderedType A} `{weak_lattice B} (f: Map [A, B]) (x: A) : B :=
  match (f)[x] with
  | Some b => b
  | None => top
  end.

Definition find_aloc (m: Map [int, d]) (v: int) : d :=
  if is_aloc v
  then find_def m v
  else ⊤.

(* A key not bound in a map is bound to bot *)
Definition find_bot {A B} `{OrderedType A} (f: Map [A, B]) (x: A) : B+⊥ :=
  match (f)[x] with
  | Some b => NotBot b
  | None => Bot
  end.

Definition ab_machine_state : Type := (ab_machine_config + d)%type.

Definition flag_LE (x y: (register * register)+⊤) : Prop :=
  match x, y with
  | _, All => True
  | All, Just _ => False
  | Just x', Just y' => x' = y'
  end.

Definition flag_LE_dec x y : { flag_LE x y } + { ¬ flag_LE x y } :=
  match x, y with
  | _, All => left I
  | All, _ => right (λ x, x)
  | Just x', Just y' => eq_dec x' y'
  end.

(* This is an ordering for maps in which keys are implicitely bound to bottom *)
Definition map_LE {A B: Type} `{OrderedType A} (leb : B → B → bool) (x y: Map [ A, B ]) : Prop :=
  ∀ a b, MapsTo a b x → ∃ b', MapsTo a b' y ∧ leb b b' = true.

Definition map_LE_dec {A B: Type} `{OrderedType A} (leb : B → B → bool) (x y: Map [ A, B ]) :
  { map_LE leb x y } + { ¬ map_LE leb x y }.
refine
  (let F r v := match (y)[r] with | Some v' => leb v v' | None => false end in
   match MF.for_all F x as b return (b = true ↔ _) → _ with
   | true => λ K, left _
   | false => λ K, right _
   end (MF.for_all_iff (f := F) _ x)).
Proof.
  subst F.
  intros a b Ha. generalize (proj1 K eq_refl a b Ha). case_eq ((y)[a]).
  2: intros _ ?; eq_some_inv.
  intros b' L. exists b'. intuition.
  subst F.
  intros K'. cut (false = true). intro; eq_some_inv.
  apply (proj2 K).
  intros k e H1. destruct (K' k e H1) as (p & P & Q).
  rewrite MF.find_mapsto_iff in P. rewrite P. exact Q.
  subst F. repeat intro. subst. rewrite MF.find_m. reflexivity. assumption. apply MF.Equal_refl.
Defined.

(* This is an ordering for maps in which keys are implicitely bound to Top *)
Definition wmap_LE {A B: Type} `{OrderedType A} `{weak_lattice B} (x y: Map [ A, B ]) : Prop :=
  ∀ a, find_def x a ⊑ find_def y a = true
     ∨ (x)[a] = (y)[a] ∧ (x)[a] = None. (* Extra property to ensure decidability
                                           (that we don’t need…) *)

Definition wmap_LE_dec {A B: Type} `{OrderedType A} `{weak_lattice B} (x y: Map [ A, B ]) :
  { wmap_LE x y } + { ¬ wmap_LE x y }.
Proof.
  assert (PR: Proper (_eq ==> eq ==> eq) (fun r v => v ⊑ find_def y r)).
    intros u u' Hu v ? ->; unfold find_def; rewrite Hu; auto.
  assert (PR': Proper (_eq ==> eq ==> eq) (fun r v => find_def x r ⊑ v)).
    intros u u' Hu v ? ->; unfold find_def; rewrite Hu; auto.

  case_eq (MF.for_all (fun r v => v ⊑ find_def y r) x);
  intros K.
  rewrite MF.for_all_iff in K. 2: auto. clear PR.
  case_eq (MF.for_all (fun r v => find_def x r ⊑ v) y);
  intros K'.
  rewrite MF.for_all_iff in K'. 2: auto. clear PR'.
  left. intros a. case_eq ((x)[a]).
  intros b Hb. left. apply K. unfold find_def. rewrite Hb. apply MF.find_mapsto_iff; auto.
  intros Ha.
  case_eq ((y)[a]).
  intros b Hb. left. apply K'. unfold find_def. rewrite Hb. apply MF.find_mapsto_iff; auto.
  intros Ha'. now right.

  right. intros N.
  cut (∀ r v, MapsTo r v y → find_def x r ⊑ v = true).
  rewrite <- MF.for_all_iff; auto. clear PR'. rewrite K'. discriminate.
  intros a b Hy.
  destruct (N a) as [N1|(N1&N1')].
  replace b with (find_def y a). apply N1.
  unfold find_def. rewrite MF.find_mapsto_iff in Hy. rewrite Hy. easy.
  exfalso. generalize (proj1 (MF.find_mapsto_iff y a b) Hy). rewrite <- N1, N1'. discriminate.

  right. intros N.
  cut (∀ r v, MapsTo r v x → v ⊑ find_def y r = true).
  rewrite <- MF.for_all_iff; auto. clear PR. rewrite K. discriminate.
  intros a b Hx.
  destruct (N a) as [N1|(N1&N1')].
  replace b with (find_def x a). apply N1.
  unfold find_def. rewrite MF.find_mapsto_iff in Hx. rewrite Hx. easy.
  exfalso. generalize (proj1 (MF.find_mapsto_iff x a b) Hx). rewrite N1'. discriminate.
Defined.

Definition abmc_LE (x y: ab_machine_config) : Prop :=
  flag_LE x.(ab_flg) y.(ab_flg)
∧ wmap_LE x.(ab_reg) y.(ab_reg)
∧ wmap_LE x.(ab_mem) y.(ab_mem).

Definition abmc_LE_dec x y : { abmc_LE x y } + { ¬ abmc_LE x y } :=
  match flag_LE_dec x.(ab_flg) y.(ab_flg) with
  | right NE => right (λ K, NE (proj1 K))
  | left F =>
    match wmap_LE_dec x.(ab_reg) y.(ab_reg) with
  | right NE => right (λ K, NE (proj1 (proj2 K)))
  | left R =>
    match wmap_LE_dec x.(ab_mem) y.(ab_mem) with
  | right NE => right (λ K, NE (proj2 (proj2 K)))
  | left MEM => left (conj F (conj R MEM))
    end
    end
  end.

Definition abms_LE (x y: ab_machine_state) : Prop :=
  match x, y with
  | inl x', inl y' => abmc_LE x' y'
  | inr x', inr y' => leb x' y' = true
  | _, _ => False
  end.

Definition abms_LE_dec x y : { abms_LE x y } + { ¬ abms_LE x y }.
Proof.
  destruct x as [x'|x']; destruct y as [y'|y']; simpl;
  try (right; intros K; exact K).
  apply abmc_LE_dec.
  apply bool_dec.
Defined.

(* Join *)
Definition flg_join x y :=
  if flag_LE_dec x y
  then y
  else All.

Definition map_join {A B: Type} `{OrderedType A} (join: B → B → B) (f g: Map [ A, B ]) : Map [ A, B ] :=
  fold
    (fun k y => add k match (f)[k] with None => y | ⌊x⌋ => join x y end)
    g
    f
.

Definition map_join_get {A B: Type} `{OrderedType A} (join : B → B → B) (f g: Map [ A, B ]) :
  ∀ k, find_bot (map_join join f g) k = match find_bot f k, find_bot g k with
                                   | NotBot x, NotBot y => NotBot (join x y)
                                   | NotBot x, Bot => NotBot x
                                   | Bot, NotBot y => NotBot y
                                   | Bot, Bot => Bot
                                   end.
Proof.
  unfold map_join, find_bot.
  apply MF.fold_rec_bis.
  intros m m' a H1 H2 k. rewrite <- (H1 k). auto.
  intros k. destruct ((f)[k]); reflexivity.
  intros k e a m' H1 H2 H3 k'.
  destruct (OrderedType.eq_dec k k') as [U|U].
  repeat rewrite MF.add_eq_o; auto. rewrite U. now destruct ((f)[k']).
  repeat rewrite MF.add_neq_o; auto.
Qed.

Definition wmap_join {A B: Type} `{OrderedType A} (join: B → B → B) `{weak_lattice B} (f g: Map [ A, B ]) : Map [ A, B ] :=
  fold
    (fun k y => let y' := join (find_def f k) y in if ⊤ ⊑ y' then id else add k y')
    g
    []
.

Definition wmap_join_get {A B: Type} `{OrderedType A} (join: B → B → B) `{weak_lattice B} (f g: Map [ A, B ]) (q:A) :
  find_def (wmap_join join f g) q = match (g)[q] with
                                    | None => (⊤)
                                    | Some y => let y' := join (find_def f q) y in
                                                if ⊤ ⊑ y' then ⊤ else y'
                                    end.
Proof.
  unfold wmap_join, find_def.
  apply MF.fold_rec_bis.
+ intros m m' a E. rewrite (MF.find_m (reflexivity q) E). exact id.
+ rewrite MF.empty_o. reflexivity.
+ intros k e a m' H1 H2 H3.
  destruct (OrderedType.eq_dec k q) as [EQ|NE].
  - (* EQ *)
    assert (K := proj1 (MF.not_find_in_iff _ _) H2). rewrite EQ in K. rewrite K in *.
    rewrite MF.add_eq_o; auto.
    rewrite (MF.find_m EQ (reflexivity f)).
    destruct (⊤ ⊑ (join _ e)). unfold id. rewrite H3. reflexivity.
    rewrite MF.add_eq_o; auto.
  - (* NE *)
    fold (find_def f k).
    destruct (⊤ ⊑ join (find_def f k) e).
    unfold id. rewrite H3.
    rewrite MF.add_neq_o; auto.
    rewrite MF.add_neq_o; auto. rewrite H3.
    rewrite MF.add_neq_o; auto.
Qed.

Definition abmc_join (x y: ab_machine_config) : ab_machine_config :=
  {| ab_flg := flg_join x.(ab_flg) y.(ab_flg)
   ; ab_reg := wmap_join join x.(ab_reg) y.(ab_reg)
   ; ab_mem := wmap_join join x.(ab_mem) y.(ab_mem) |}.

Definition abmc_widen (x y: ab_machine_config) : ab_machine_config :=
  {| ab_flg := flg_join x.(ab_flg) y.(ab_flg)
   ; ab_reg := wmap_join widen x.(ab_reg) y.(ab_reg)
   ; ab_mem := wmap_join widen x.(ab_mem) y.(ab_mem) |}.

Definition abms_join (x y: ab_machine_state) : ab_machine_state+⊤ :=
  match x, y with
  | inl x', inl y' => Just (inl (abmc_join x' y'))
  | inr x', inr y' => Just (inr (join x' y'))
  | _, _ => All
  end.

(* Gamma *)
Definition flg_gamma (x: (register * register)+⊤) (mci: machine_config) : Prop :=
  match x with
  | Just (r1, r2) => ∀ f, mci.(mc_flg) f = eval_flag (mci.(mc_reg) r2) (mci.(mc_reg) r1) f
  | All => True
  end.

Definition map_gamma {A B C: Type} `{OrderedType A} `{weak_lattice B} `{gamma_op B C} (x: Map [ A, B ]) (v: A → C): Prop :=
  ∀ k, γ (find_bot x k) (v k).

Lemma map_join_sound {A B C: Type} `{OrderedType A} `{WL:weak_lattice B}
      `{G:gamma_op B C} `{adom B C WL G} :
  ∀ P, Proper (_eq ==> eq) P →
       ∀ x y: Map [ A, B ],
         map_gamma x P ∨ map_gamma y P → map_gamma (map_join join x y) P.
Proof.
  intros P PR x y. unfold map_gamma. intros Hxy k.
  rewrite map_join_get.
  destruct (find_bot x k) eqn: XK;
  destruct (find_bot y k) eqn: YK;
  (destruct Hxy as [K|K];
   specialize (K k);
   [rewrite XK in K|rewrite YK in K]
  );
  auto;
  (try now destruct K);
  apply join_sound; auto.
Qed.

Definition wmap_gamma {A B C: Type} `{OrderedType A} `{weak_lattice B} `{gamma_op B C} (x: Map [ A, B ]) (v: A → C): Prop :=
  ∀ k, γ (find_def x k) (v k).

Lemma wmap_join_sound {A B C: Type} `{OrderedType A} `{WL: weak_lattice B} `{G: gamma_op B C} `{AD: adom _ _ WL G} (x y: Map [ A, B ]) :
  ∀ P, Proper (_eq ==> eq) P →
  wmap_gamma x P ∨ wmap_gamma y P → wmap_gamma (wmap_join join x y) P.
Proof.
  intros P PP. unfold wmap_gamma. intros Hxy k. rewrite wmap_join_get.
  destruct ((y)[k]) eqn: YK. 2: apply gamma_top, AD.
  simpl.
  destruct (⊤ ⊑ _). apply gamma_top, AD.
  apply (join_sound _ _ _ _ AD).
  destruct Hxy as [K|K]; specialize (K k).
  left; exact K.
  unfold find_def in K. rewrite YK in K. right; exact K.
Qed.

Definition gamma_mem {C: Type} `{G: gamma_op d C} (x: Map [ int, d ]) (v: int → C) : Prop :=
  ∀ k, v(k) ∈ γ(find_aloc x k).

Lemma gamma_mem_sound {C: Type} `{G: gamma_op d C} `{AD: adom _ _ _ G} (x y: Map [ int, d ]) :
  (gamma_mem x ∪ gamma_mem y) ⊆ gamma_mem (wmap_join join x y).
Proof.
  intros a H k.
  unfold find_aloc.
  destruct (is_aloc k) eqn: K.
  rewrite wmap_join_get.
  destruct ((y)[k]) eqn: YK.
  2: apply gamma_top; auto.
  simpl. destruct (⊤ ⊑ _).
  apply gamma_top; auto.
  unfold gamma_mem, find_aloc in H.
  destruct H as [H|H];
  specialize (H k);
  rewrite K in H;
  apply join_sound; auto.
  right. revert H. unfold find_def, addr. rewrite YK. exact id.
  apply gamma_top; auto.
Qed.

Definition abmc_gamma (x: ab_machine_config) (mc: machine_config) : Prop :=
    flg_gamma x.(ab_flg) mc
  ∧ wmap_gamma x.(ab_reg) mc.(mc_reg)
  ∧ gamma_mem x.(ab_mem) mc.(mc_mem).

Definition abms_gamma (x: ab_machine_state) (m: machine_state) : Prop :=
  match x, m with
  | inl x', Running m' => abmc_gamma x' m'
  | inr x', Halted m' => γ x' m'
  | _, _ => False
  end.

Definition map_to_string {A B: Type} `{OrderedType A}
           (A_to_string : A → string) (B_to_string : B → string)
           (m: Map [A,B]) : string  :=
  (fold
    (fun k v acc => A_to_string k ++ " ↦ " ++ B_to_string v ++ "; " ++ acc)
    m
    ""
  )%string.

Instance abmc_toString `{ToString d} : ToString ab_machine_config :=
  { to_string x :=
  ("⟨" ++
    match x.(ab_flg) with
    | All => ""
    | Just (r1,r2) => "(" ++ string_of_reg r1 ++ ", " ++ string_of_reg r2 ++ ")"
    end ++
    map_to_string string_of_reg to_string x.(ab_reg) ++
    map_to_string string_of_int to_string x.(ab_mem) ++
    "⟩"
  )%string
  }.

Definition ab_machine_config_pl : pre_lattice ab_machine_config :=
  {| pl_leb x y := abmc_LE_dec x y
   ; pl_join x y := Just (abmc_join x y)
   ; pl_widen x y := Just (abmc_widen x y)
  |}.

Lemma ab_machine_config_pl_sound : pre_lattice_spec ab_machine_config_pl abmc_gamma.
Proof.
  Hint Resolve as_int_adom.
  split.
+ (* gamma monotone *)
  intros x y. simpl.
  destruct abmc_LE_dec as [LE|]. 2: intro; exfalso; discriminate.
  intros _ mci.
  destruct x as [xf xr xm];
  destruct y as [yf yr ym].
  destruct LE as (LEf & LEr & LEm).
  intros (f & r & m). simpl in *.
  split; simpl.
  destruct xf as [|(xf1,xf2)]; destruct yf as [|(yf1,yf2)]; auto.
  exact (False_ind _ LEf).
  simpl in *. intuition congruence.
  split.
  intros k. generalize (LEr k). unfold find_def.
  destruct ((yr)[k]); auto.
  generalize (r k). unfold find_def. destruct ((xr)[k]); intros u [v|(K&K')]; try (exfalso; discriminate); auto; eapply gamma_monotone; eauto.
  intros _. apply gamma_top; auto.
  intros k.
  unfold find_aloc. destruct (is_aloc k) eqn: K.
  2: apply gamma_top; auto.
  generalize (LEm k). unfold find_def.
  destruct ((ym)[k]); auto.
  2: intros _; apply gamma_top; auto.
  generalize (m k). unfold find_aloc. rewrite K.
  unfold find_def. destruct ((xm)[k]); intros u [v|(?&?)]; try (exfalso; discriminate); auto; eapply gamma_monotone; eauto.
+ (* join sound *)
  intros x y; simpl.
  unfold γ, abmc_gamma. simpl.
  intros mci H.
  destruct x as [xf xr xm];
  destruct y as [yf yr ym]; simpl in *.
  split.
  destruct xf as [|(xf1,xf2)]; destruct yf as [|(yf1,yf2)]; simpl; auto.
  unfold flg_join. destruct flag_LE_dec; simpl in *. intuition. congruence. exact I.
  split.
  apply (wmap_join_sound (AD := as_int_adom)). intros u v K. rewrite (register_eq_eq K). auto.
  intuition.
  apply (gamma_mem_sound (AD := as_int_adom)). intuition.
Qed.

Definition invalidate_flag (r:register) f :=
match f with
| All => All
| Just (r1, r2) => if eq_dec r r1 then All else if eq_dec r r2 then All else f
end.

Lemma invalidate_flag_preserve : forall {R F p1 p2},
  invalidate_flag R F = Just (p1,p2) →
  R ≠ p1 ∧ R ≠ p2.
Proof.
  unfold invalidate_flag.
  intros R [|[r1 r2]] q1 q2. intro; exfalso; discriminate.
  destruct @eq_dec. intro; exfalso; discriminate.
  destruct @eq_dec. intro; exfalso; discriminate.
  injection 1. repeat intros ->. intuition.
Qed.

Definition ab_store_strong (m: Map [ addr, d ]) (a: addr) (v: d) : Map [ addr, d ] :=
  if is_aloc a
  then if ⊤ ⊑ v
       then remove a m
       else (m)[a <- v]
  else m.


Definition abmc_init (m: memory) (dom: list int) : Map [ int, d ] :=
  List.fold_left (fun a i => (a)[ i <- const_int (m i) ]) dom [].

Definition ab_machine_config_mem_dom : mem_dom (ab_machine_config+⊤) d :=
{|
  as_wl := weak_lattice_of_pre_lattice ab_machine_config_pl
; var x := match x with
           | Just x' => find_def x'.(ab_reg)
           | _ => fun _ => top
           end
; load_single x := match x with
                   | Just x' => find_aloc x'.(ab_mem)
                   | _ => fun _ => top
                   end
; compare x := match x with
               | Just x' => fun r1 r2 => Just {| ab_flg := Just (r1, r2)
                                               ; ab_reg := x'.(ab_reg)
                                               ; ab_mem := x'.(ab_mem) |}
               | _ => fun _ _ => x
               end
; assume x := match x with
              | Just x' =>
                fun f =>
                  match x'.(ab_flg) with
                  | Just (Ru, Rv) =>
                    fun b =>
                      let u := find_def x'.(ab_reg) Ru in
                      let v := find_def x'.(ab_reg) Rv in
                      let op := match f with FLE => Cle | FLT => Clt | FEQ => Ceq end in
                      let v'u' := backward_int_binop (OpCmp op) v u
                                                 (const_int (IntervalDomain.Interval.of_bool b)) in
                      match v'u' with
                      | (NotBot v', NotBot u') =>
                        NotBot (Just {| ab_flg := x'.(ab_flg)
                                      ; ab_reg := (x'.(ab_reg)) [ Ru <- u' ] [ Rv <- v' ]
                                      ; ab_mem := x'.(ab_mem) |})
                      | _ => Bot
                      end
                  | All => fun _ => NotBot x
                end
              | All => fun _ _ => NotBot All
              end
; assign x := match x with
              | Just x' => fun r v => Just {| ab_flg := invalidate_flag r x'.(ab_flg)
                                            ; ab_reg := (x'.(ab_reg)) [ r <- v ]
                                            ; ab_mem := x'.(ab_mem) |}
              | _ => fun _ _ => All
              end
; store_single x a v := do_top x' <- x; 
                        Just {| ab_flg := x'.(ab_flg)
                              ; ab_reg := x'.(ab_reg)
                              ; ab_mem := ab_store_strong x'.(ab_mem) a v |}
; init m dom := Just {| ab_flg := All; ab_reg := []; ab_mem := abmc_init m dom |}
|}.

Lemma ab_machine_config_mem_dom_sound : mem_dom_sound ab_machine_config_mem_dom (toplift_gamma abmc_gamma).
Proof.
  constructor.
- (* adom *)
  eapply adom_of_pre_lattice, ab_machine_config_pl_sound.
- (* var *)
  intros [|m'] m H r; simpl. apply gamma_top, as_int_adom. apply H.
- (* load *)
  intros [|m'] m H a; simpl.
  apply gamma_top, as_int_adom.
  apply H.
- (* assign *)
  intros [|m'] rd v a (m & v' & H & K & L & M & N). auto.
  destruct H as (HF & HR & HM).
  split; simpl.
  unfold invalidate_flag. destruct m'.(ab_flg) as [|(r1,r2)]. auto.
  destruct @eq_dec. exact I.
  destruct @eq_dec. exact I.
  simpl. simpl in HF. intros f. rewrite L, M.
  repeat rewrite upd_o; auto.
  rewrite M, N. clear M N.
  split; auto.
  intros r. unfold find_def.
  unfold upd. destruct @eq_dec. subst. rewrite MF.add_eq_o; auto.
  rewrite MF.add_neq_o. apply HR. apply register_neq_neq. intuition.
- (* store *)
  intros [|ab] dst v mc H. exact I.
  destruct H as (m & v' & (HF & HR & HM) & V & M).
  simpl in *.
  split. exact HF. split. exact HR.
  intros k. simpl. unfold ab_store_strong.
  rewrite M.
  unfold find_aloc.
  destruct (is_aloc k) eqn: AL. 2: apply gamma_top; auto.
  destruct (eq_dec dst k) as [ -> | NE ].
  rewrite AL.
  destruct (⊤ ⊑ v); unfold find_def.
  rewrite MF.remove_eq_o; auto. apply gamma_top; auto.
  rewrite MF.add_eq_o; auto. rewrite upd_s. exact V.
  generalize (HM k). unfold find_aloc. rewrite AL.
  rewrite upd_o; auto.
  destruct (is_aloc dst). 2: exact id.
  intros H.
  destruct (⊤ ⊑ v); unfold find_def.
  rewrite MF.remove_neq_o; auto.
  rewrite MF.add_neq_o; auto.
- (* compare *)
  intros [|m']. easy.
  intros rs rd a (f & H & U).
  split; simpl. congruence.
  split; apply H.
- (* assume *)
  intros [|[[|(f1,f2)] r' m']]; try easy;
  intros f b a (A&B). auto.
  destruct A as (HF&HR&HM). simpl in *.
  match goal with |- context[ backward_int_binop ?o ?x ?y ?z ] =>
                  generalize (backward_int_binop_sound o x y z)
  end.
  destruct backward_int_binop as (x',y').
  intros H. destruct (H (mc_reg a f2) (mc_reg a f1)) as (Hx,Hy); auto.
  specialize (HF f). rewrite B in HF. rewrite HF.
  destruct f; apply const_int_correct.
  destruct x'. exact Hx.
  destruct y'. exact Hy.
  split; simpl. auto. split; auto.
  intros k. unfold find_def.
  destruct (OrderedType.eq_dec f2 k) as [U|U].
  rewrite MF.add_eq_o; auto. rewrite <- (register_eq_eq U). auto.
  rewrite MF.add_neq_o; auto.
  destruct (OrderedType.eq_dec f1 k) as [V|V].
  rewrite MF.add_eq_o; auto. rewrite <- (register_eq_eq V). auto.
  rewrite MF.add_neq_o; auto.
  apply HR.
- (* Flow insensitive *)
  intros [|x] m H pp. auto. apply H.
- (* init *)
  intros m [pp0 m0 r f] dom. simpl.
  intros (->, I).
  split. easy. split. simpl. intros k. unfold wmap_gamma, find_def. apply gamma_top; auto.
  simpl. unfold abmc_init, gamma_mem.
  induction dom as [|x dom IH] using rev_ind;
  intros k.
  unfold find_aloc. destruct is_aloc; apply gamma_top; auto.
  rewrite fold_left_app. simpl.
  unfold find_aloc. destruct (is_aloc k) eqn: K. 2: apply gamma_top; auto.
  unfold find_def.
  destruct (OrderedType.eq_dec x k) as [U|U].
  rewrite MF.add_eq_o; auto. rewrite I, U. apply const_int_correct.
  rewrite MF.add_neq_o; auto.
  generalize (IH k). unfold find_aloc. rewrite K. exact id.
Qed.

End AbMachineConfig.
