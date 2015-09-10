Require Import Omega.

Require Export SFC.Typing.
Require Import SFC.SystemFC.
Require Import SFC.Shifting.
Require Import SFC.Substitution.
Require Export Logic.Decidable.

(** This module contains various properties related to 
    Weakening and Strengthening for the type system. 

    It is divided into three parts: lemmas related to type variables, coercion
    variables and term variables.
    
  
*)


(* ####################################################### *)  
(* ** Context manipulation with type variables.            *)
(* ####################################################### *)  

(* The important properties of this section are that the three 
   judgments are stable under weakening by type variables. 
 *)


(* insert_var n k G G' means that G' is G extended with a 
   new type variable at location n. *)
Inductive insert_tvar : nat -> kind -> context -> context -> Prop :=
  | it_here : forall Gamma k,
 (*     well_formed_type Gamma T k -> *)
      insert_tvar 0 k Gamma (ext_tvar Gamma k)
  | it_var : forall X k T Gamma Gamma',
      insert_tvar X k Gamma Gamma' ->
      insert_tvar X k (ext_var Gamma T) (ext_var Gamma' (tshift X T))
  | it_bound : forall X k k' Gamma Gamma',
      insert_tvar X k Gamma Gamma' ->
      insert_tvar (S X) k (ext_tvar Gamma k') (ext_tvar Gamma' k')
  | it_cvar : forall X k Gamma Gamma' U V,
      insert_tvar X k Gamma Gamma' ->
      insert_tvar X k (ext_cvar Gamma (U, V))
                  (ext_cvar Gamma' (tshift X U, tshift X V)).

Lemma get_tvar_insert_ge : forall Gamma Gamma' n k m,
  insert_tvar n k Gamma Gamma' ->
  n <= m                     ->
  get_tvar Gamma' (S m) = get_tvar Gamma m.
Proof.
  intros. generalize dependent m.
  induction H; intros. 
    simpl. trivial.
    simpl. apply IHinsert_tvar. trivial.
    simpl. destruct m. omega.
      apply IHinsert_tvar. omega.
    simpl. apply IHinsert_tvar. trivial.
Qed.

Lemma get_tvar_insert_lt : forall Gamma Gamma' n k m,
  insert_tvar n k Gamma Gamma' ->
  n > m                      ->
  get_tvar Gamma' m = get_tvar Gamma m.
Proof.
  intros. generalize dependent m.
  induction H; intros. 
    simpl. omega.
    simpl. apply IHinsert_tvar. trivial.
    simpl. destruct m. trivial.
      apply IHinsert_tvar. omega.
    simpl. apply IHinsert_tvar. trivial.
Qed.

Lemma insert_tvar_wf_type : forall Gamma Gamma' U k' n k,
  insert_tvar n k Gamma Gamma' ->
  well_formed_type Gamma U k'  ->
  well_formed_type Gamma' (tshift n U) k'.
Proof.
  intros. generalize dependent Gamma. generalize dependent Gamma'. 
  generalize dependent n. generalize dependent k'. induction U; intros.
    simpl. constructor. destruct (le_gt_dec n0 n); inversion H0;
      rewrite <- H2. eapply get_tvar_insert_ge. apply H. omega.
    eapply get_tvar_insert_lt. apply H. omega.
    simpl. inversion H0.  subst. constructor.  trivial. 
    simpl. inversion H0. subst. eapply WF_TApp with k'0. eapply IHU1. apply H.
      trivial. eapply IHU2. apply H. trivial.
    simpl. inversion H0. constructor. eapply IHU. constructor. apply H.
      inversion H0. trivial.
Qed.


Lemma insert_tvar_wf_context : forall Gamma Gamma' n k,
  insert_tvar n k Gamma Gamma' ->
  well_formed_context Gamma  ->
  well_formed_context Gamma'.
Proof.
  intros. induction H; try constructor.
    trivial.
    eapply insert_tvar_wf_type. apply H. inversion H0. trivial.
      apply IHinsert_tvar. inversion H0. trivial.
    apply IHinsert_tvar. inversion H0. trivial.
    inversion H0. apply WFC_ext_cvar with k0.
       apply IHinsert_tvar. trivial.
       eapply insert_tvar_wf_type. apply H. trivial.
       eapply insert_tvar_wf_type. apply H. trivial.
Qed.    

Lemma get_var_insert_tvar : forall Gamma Gamma' x X k,
  insert_tvar X k Gamma Gamma' ->
  get_var Gamma' x = opt_map (tshift X) (get_var Gamma x).
Proof.
  intros. generalize dependent x. induction H; intros; simpl.
    trivial.
    destruct x.
      trivial.
      apply IHinsert_tvar.
    rewrite IHinsert_tvar. destruct (get_var Gamma x).
      simpl. apply f_equal. assert (X = 0 + X) by trivial. 
      rewrite H0. rewrite tshift_tshift_prop. trivial.
      trivial.
    rewrite IHinsert_tvar. trivial.
Qed.

Lemma get_cvar_insert_tvar : forall Gamma Gamma' x X k,
  insert_tvar X k Gamma Gamma' ->
  get_cvar Gamma' x = opt_map_prod (tshift X) (get_cvar Gamma x).
Proof.
  intros; generalize dependent x; induction H; intros; trivial.
  Case "ext_var".
    simpl. apply IHinsert_tvar.
  Case "ext_tvar".
    simpl. rewrite IHinsert_tvar. destruct get_cvar.
      destruct p. simpl. apply f_equal.
        assert (X = O + X) by trivial. rewrite H0. rewrite tshift_tshift_prop.
        rewrite tshift_tshift_prop. trivial.
        trivial.
  Case "ext_cvar".      
    simpl. destruct x. trivial. apply IHinsert_tvar.
Qed.

Lemma coercion_weakening_tvar_ind : forall Gamma Gamma' c n k U V,
  insert_tvar n k Gamma Gamma' ->
  Gamma  |- c ; U ~~ V ->
  Gamma' |- cshift_typ n c ; tshift n U ~~ tshift n V.
Proof.
  intros; generalize dependent Gamma'; generalize dependent n;
  coercion_cases (induction H0) Case; intros; simpl; try constructor;
  try (eapply C_Refl; eauto);
  try (eapply C_Trans); try (eapply C_App);
  try (eapply C_ALeft; eauto);
  try (eapply C_ARight; eauto);
  try (eapply C_Inst; eauto);
  try (eapply insert_tvar_wf_context; eassumption; trivial);
  try (apply IHwell_formed_coercion; trivial);
  try (apply IHwell_formed_coercion1; trivial);
  try (apply IHwell_formed_coercion2; trivial);
  try (apply IHwell_formed_coercion3; trivial).
  Case "C_Var".    
    rewrite get_cvar_insert_tvar with Gamma Gamma' x n k.
    rewrite H0. simpl. trivial. trivial. 
  Case "C_Refl".
    eapply insert_tvar_wf_type. eassumption. eauto. 
    Case "C_App".
    pose (J := insert_tvar_wf_type _ _ _ _ _ _ H1 H). assumption.
    pose (J := insert_tvar_wf_type _ _ _ _ _ _ H1 H0). assumption.
  Case "C_Forall".
  constructor. trivial.
    pose (J := insert_tvar_wf_type _ _ _ _ _ _ H2 H). assumption.
    pose (J := insert_tvar_wf_type _ _ _ _ _ _ H2 H1). assumption.  
  Case "C_ALeft".
    eapply insert_tvar_wf_type; eauto.
    eapply insert_tvar_wf_type; eauto.
  Case "C_ARight".
    eapply insert_tvar_wf_type; eauto.
    eapply insert_tvar_wf_type; eauto.
  Case "C_Inst".    
    assert (n = 0 + n) by trivial. rewrite H2. rewrite tshift_subst_prop_2.
    rewrite tshift_subst_prop_2.
    eapply C_Inst.
    apply IHwell_formed_coercion.
    trivial.
    eapply insert_tvar_wf_type. eassumption. trivial.
Qed.


Lemma typing_weakening_tvar_ind : forall Gamma Gamma' n k t U,
  insert_tvar n k Gamma Gamma' ->
  Gamma  |- t \in U          ->
  Gamma' |- shift_typ n t \in tshift n U.
Proof.
  intros. generalize dependent n. generalize dependent Gamma'.
  has_type_cases (induction H0) Case; intros; simpl.
  Case "T_Var".
    constructor. eapply insert_tvar_wf_context. apply H1.
    trivial. rewrite get_var_insert_tvar with Gamma Gamma' x n k.
    rewrite H0. trivial. trivial.
  Case "T_Abs".
  constructor. apply insert_tvar_wf_type with Gamma k; eauto.
  apply IHhas_type. constructor. trivial.
  Case "T_App".
    apply T_App with (tshift n T11). simpl in IHhas_type1.
    apply IHhas_type1. trivial. apply IHhas_type2. trivial.
  Case "T_TAbs".
    constructor. apply IHhas_type. constructor. trivial.
  Case "T_TApp".
    assert (n = 0 + n) by trivial. rewrite H3. rewrite tshift_subst_prop_2.
    eapply T_TApp. apply IHhas_type. trivial. eapply insert_tvar_wf_type.
    apply H2. trivial. eapply insert_tvar_wf_context. apply H2.
    trivial.
  Case "T_CAbs".
    constructor. apply IHhas_type. constructor. trivial.
    eapply insert_tvar_wf_type. eassumption. trivial.
    eapply insert_tvar_wf_type. eassumption. trivial.
  Case "T_CApp".
    econstructor. simpl in IHhas_type. apply IHhas_type. trivial.
    eapply coercion_weakening_tvar_ind. eassumption. trivial.
  Case "T_Coerce".
    econstructor. eapply coercion_weakening_tvar_ind. eassumption. eassumption.
    apply IHhas_type. trivial.
Qed.


(* ** ----  Top level type weakening theorems ------ *)

Lemma type_weakening_tvar : forall U Gamma k k',
  well_formed_type Gamma U k ->
  well_formed_type (ext_tvar Gamma k') (tshift 0 U) k.
Proof.
  intros.
  apply insert_tvar_wf_type with Gamma k'. 
  constructor. auto.
Qed.

Lemma coercion_weakening_tvar :forall Gamma c U V k,
  Gamma |- c ; U ~~ V ->
  (ext_tvar Gamma k) |- (shift_typ 0 c) ; (tshift 0 U) ~~ (tshift 0 V).
  Proof.
    intros. apply coercion_weakening_tvar_ind with Gamma k.
    constructor. auto.
Qed.  

Lemma term_weakening_tvar : forall Gamma t k U,
  Gamma |- t \in U ->
  ext_tvar Gamma k |- shift_typ 0 t \in tshift 0 U.
Proof.
  intros. eapply typing_weakening_tvar_ind. econstructor. auto.
Qed.

(* ** ---- Alternative: no shifting necessary for closed types ------- *)

Fixpoint num_tvars (Gamma:context) : nat :=
  match Gamma with
    | empty => 0
    | ext_var Gamma _ => num_tvars Gamma
    | ext_tvar Gamma _ => 1 + num_tvars Gamma
    | ext_cvar Gamma _ => num_tvars Gamma
  end.

Lemma tvar_index_bound : forall Gamma x k,
  get_tvar Gamma x = Some k ->
  x < num_tvars Gamma.
Proof.
  intros. generalize dependent x.
  induction Gamma; intros.
    inversion H.
    simpl. simpl in H. apply IHGamma. trivial.
    simpl. destruct x.
      omega. assert (x < num_tvars Gamma -> S x < S (num_tvars Gamma)) by omega.
      apply H0. eapply IHGamma. eassumption.
    simpl. simpl in H. apply IHGamma. trivial.
Qed. 

Lemma no_tvars_tshift_ind : forall Gamma T k n,
  well_formed_type Gamma T k ->
  num_tvars Gamma = n      ->
  tshift n T = T.
Proof.
  intros. generalize dependent Gamma; generalize dependent n. generalize dependent k.
  induction T; intros; inversion H; subst.
  Case "TVar".
    assert (n < num_tvars Gamma). apply tvar_index_bound with k. trivial.
    simpl. destruct le_gt_dec. omega. trivial.
  Case "TCon".
    simpl. trivial.
  Case "TApp".
    simpl. erewrite IHT1. erewrite IHT2. trivial. eassumption. trivial.
    eassumption. trivial.
  Case "TUniv".
    simpl. erewrite IHT. trivial. eassumption. simpl. trivial.
Qed.

Lemma no_cvars_cshift_typ_ind : forall Gamma c U V n,
  Gamma |- c ; U ~~ V ->
  num_tvars Gamma = n ->
  cshift_typ n c = c.
Proof with eauto.
  intros. generalize dependent n. coercion_cases (induction H) Case; intros; simpl;
  try (erewrite IHwell_formed_coercion);
  try (erewrite IHwell_formed_coercion1);
  try (erewrite IHwell_formed_coercion2);
  try (erewrite IHwell_formed_coercion3)...
  Case "C_Refl".
    erewrite no_tvars_tshift_ind. trivial. eassumption. trivial.
  Case "C_Forall".
    simpl. omega.
  Case "C_Inst".
    erewrite no_tvars_tshift_ind. trivial. eassumption. trivial.
Qed.

Lemma no_tvars_shift_typ_ind : forall Gamma t T n,
  Gamma |- t \in T ->
  num_tvars Gamma = n ->
  shift_typ n t = t.
Proof.
  intros. generalize dependent T. generalize dependent n.
  generalize dependent Gamma.
  t_cases (induction t) Case; intros; inversion H; subst.
  Case "tvar".
    simpl. trivial.
  Case "tapp".
    simpl. erewrite IHt1. erewrite IHt2. trivial. reflexivity.
    eassumption. reflexivity. eassumption.
  Case "tabs".
    simpl. erewrite (IHt (ext_var Gamma t)). erewrite no_tvars_tshift_ind.
    trivial. eauto. trivial. simpl. trivial. eassumption. 
  Case "ttapp".
    simpl. erewrite IHt. erewrite no_tvars_tshift_ind. trivial. eassumption.
    trivial. reflexivity. eassumption.
  Case "ttabs".
    simpl. erewrite (IHt (ext_tvar Gamma k)); trivial. eassumption.
  Case "tcapp".
    simpl. erewrite IHt. erewrite no_cvars_cshift_typ_ind. trivial. eassumption.
    trivial. reflexivity. eassumption.
  Case "tcabs".
    simpl. erewrite (IHt (ext_cvar Gamma (t, t0))). erewrite no_tvars_tshift_ind.
    erewrite no_tvars_tshift_ind. trivial. eassumption. trivial. eassumption.
    trivial. trivial. eassumption.
  Case "tcoerce".
    simpl. erewrite IHt. erewrite no_cvars_cshift_typ_ind. trivial. eassumption.
    trivial. reflexivity. eassumption.
Qed.


(* ####################################################### *)  
(** ** Context manipulation with coercion variables.       *)
(* ####################################################### *)

(** Coercion variables can be weakened in all judgments and 
   can be strengthened in the type and context well-formedness
   judgments. *)

Fixpoint remove_cvar (Gamma : context) (x : nat) : context :=
  match Gamma with
  | empty            => empty
  | ext_tvar Gamma' k  => ext_tvar (remove_cvar Gamma' x) k
  | ext_var Gamma' T => ext_var (remove_cvar Gamma' x) T
  | ext_cvar Gamma' (U, V) =>
    match x with
      | O   => Gamma'
      | S y => ext_cvar (remove_cvar Gamma' y) (U, V)
    end
  end.

Lemma remove_cvar_get_tvar : forall Gamma X x,
  get_tvar Gamma X = get_tvar (remove_cvar Gamma x) X.
Proof with eauto.
  induction Gamma; intros; try (destruct X); try (destruct p; destruct x);
  simpl; trivial.
Qed.

(* ------------------------------------------- *)
(** Coercion variable strengthening            *)
(* ------------------------------------------- *)

Lemma type_strengthening_remove_cvar : forall Gamma X T k,
  well_formed_type Gamma T k ->
  well_formed_type (remove_cvar Gamma X) T k.
Proof.
  intros. generalize dependent X; generalize dependent Gamma;
          generalize dependent k;
          induction T; intros; try constructor; inversion H.
  Case "TVar".
    subst. rewrite <- remove_cvar_get_tvar. trivial.
  Case "TCon".
    trivial.
    Case "TApp".
    inversion H.
    apply WF_TApp with k'.     apply IHT1; trivial. apply IHT2; trivial.
  Case "TUniv".
    inversion H. constructor.
    eapply IHT in H3. simpl in H3. apply H3.
Qed.

Lemma context_strengthening_remove_cvar : forall Gamma X,
  well_formed_context Gamma ->
  well_formed_context (remove_cvar Gamma X).
Proof.
  induction Gamma; intros.
  Case "empty".
    constructor.
  Case "ext_var".
  simpl. constructor. inversion H; subst.
  apply type_strengthening_remove_cvar.
    trivial. apply IHGamma. inversion H. trivial.
  Case "ext_tvar".
    simpl. constructor. apply IHGamma. inversion H. trivial.
  Case "ext_cvar".
    simpl. inversion H; subst. destruct X. trivial.
    apply WFC_ext_cvar with k. apply IHGamma. trivial.
    apply type_strengthening_remove_cvar. trivial.
    apply type_strengthening_remove_cvar. trivial.
Qed.


(* ------------------------------------------- *)
(** Coercion variable weakening in types       *)
(* ------------------------------------------- *)

Lemma type_remove_cvar : forall Gamma X T k,
  well_formed_type (remove_cvar Gamma X) T k ->
  well_formed_type Gamma T k.
Proof.
  intros. generalize dependent X; generalize dependent k;
          generalize dependent Gamma; 
          induction T; intros; inversion H; try constructor.
  Case "TVar".
    subst. erewrite remove_cvar_get_tvar. apply H1.
    Case "TCon".
    trivial.
    Case "TApp".
    eapply WF_TApp.
    eapply IHT1; apply H2. eapply IHT2; apply H4.
  Case "TUniv".
    eapply IHT. simpl. apply H3.
Qed.

Lemma type_weakening_cvar : forall Gamma U V T k,
  well_formed_type Gamma T k ->
  well_formed_type (ext_cvar Gamma (U, V)) T k.
Proof.
  intros. apply type_remove_cvar with 0. simpl. trivial.
Qed.

(* ------------------------------------------- *)
(** Coercion variable weakening in coercions   *)
(* ------------------------------------------- *)


Lemma get_cvar_remove_lt : forall Gamma x y,
   x < y ->
   get_cvar Gamma x = get_cvar (remove_cvar Gamma y) x.
Proof.
  induction Gamma; intros.
  Case "empty".
    trivial.
  Case "ext_var".
    simpl. apply IHGamma. trivial.
  Case "ext_tvar".
    simpl. erewrite IHGamma. reflexivity. trivial.
  Case "ext_cvar".
    simpl. destruct x; destruct p; destruct y; try omega; trivial.
    simpl. apply IHGamma. omega.
Qed.

Lemma get_cvar_remove_ge : forall Gamma x y,
   x >= y ->
   get_cvar Gamma (S x) = get_cvar (remove_cvar Gamma y) x.
Proof.
  induction Gamma; intros.
  Case "empty".
    trivial.
  Case "ext_var".
    simpl. apply IHGamma. trivial.
  Case "ext_tvar".
    simpl. erewrite IHGamma. reflexivity. trivial.
  Case "ext_cvar".
    simpl. destruct x; destruct p; destruct y; try omega; trivial.
    simpl. apply IHGamma. omega.
Qed.

Lemma coercion_weakening_ind : forall Gamma c X U V,
  well_formed_context Gamma ->
  remove_cvar Gamma X |- c ; U ~~ V ->
  Gamma |- cshift X c ; U ~~ V.
Proof.
  intros; remember (remove_cvar Gamma X) as G; generalize dependent Gamma;
  coercion_cases (induction H0) Case; intros; subst; simpl;
  try (constructor; trivial);
  try (eapply C_Refl; eauto);
  try (eapply C_Trans); try (eapply C_App);
  try (eapply C_ALeft; eauto);
  try (eapply C_ARight; eauto);
  try (eapply C_Inst; eauto);
  try (eapply type_remove_cvar; eauto);
  try (eapply IHwell_formed_coercion; trivial);
  try (eapply IHwell_formed_coercion1; trivial);
  try (eapply IHwell_formed_coercion2; trivial);
  try (eapply IHwell_formed_coercion3; trivial).
  Case "C_Var".
    destruct (le_gt_dec X x); rewrite <- H0.
    SCase "X <= n".
      apply get_cvar_remove_ge; omega.
    SCase "X > n".
      apply get_cvar_remove_lt; omega.
  Case "C_Forall".
    constructor. trivial.
Qed.

Lemma coercion_weakening : forall Gamma c U V U' V' k,
  well_formed_context Gamma ->
  Gamma |- c ; U ~~ V ->
  well_formed_type Gamma U' k ->
  well_formed_type Gamma V' k ->
  ext_cvar Gamma (U', V') |- cshift 0 c ; U ~~ V.
Proof.
  intros.
  apply coercion_weakening_ind. apply WFC_ext_cvar with k; auto.
  simpl. auto.
Qed.

(* ------------------------------------------- *)
(** Coercion variable weakening in terms       *)
(* ------------------------------------------- *)

Lemma remove_cvar_get_var : forall Gamma x y,
  get_var Gamma x = get_var (remove_cvar Gamma y) x.
Proof.
  induction Gamma; intros; try (destruct x); try (destruct p); try (destruct y);
  simpl; try (apply f_equal); simpl; trivial.
Qed.

Lemma typing_weakening_cvar_ind : forall Gamma x t T,
  well_formed_context Gamma      ->
  remove_cvar Gamma x |- t \in T ->
  Gamma |- shift_cn x t \in T.
Proof.
  intros Gamma x t; generalize dependent Gamma; generalize dependent x;
  t_cases (induction t) Case; intros; simpl; inversion H0; subst; econstructor;
  try (apply IHt1; trivial; eassumption);
  try (apply IHt2; trivial; eassumption);
  try (apply IHt; try constructor; trivial; simpl; trivial);
  try (eapply type_remove_cvar; eassumption; trivial); trivial.
  Case "tvar".
    trivial. erewrite remove_cvar_get_var. eassumption.
  Case "tcapp".
    eassumption. apply coercion_weakening_ind. trivial. trivial.
  Case "tcabs".
  eapply WFC_ext_cvar. eauto.
  eapply type_remove_cvar; eauto.
  eapply type_remove_cvar; eauto.
  Case "tcoerce".
    apply coercion_weakening_ind. trivial. eassumption.
    trivial.
Qed.

Lemma typing_weakening_cvar : forall Gamma t T U V k,
  well_formed_context Gamma      ->
  Gamma |- t \in T ->
  well_formed_type Gamma U k ->
  well_formed_type Gamma V k ->                   
  ext_cvar Gamma (U,V) |- shift_cn 0 t \in T.
Proof.
  intros. apply typing_weakening_cvar_ind.
  econstructor; eauto.
  simpl. auto.
Qed.

(* ------- weakening without shifting  ------------------ *)

Fixpoint num_cvars (Gamma:context) : nat :=
  match Gamma with
    | empty => 0
    | ext_var Gamma _ => num_cvars Gamma
    | ext_tvar Gamma _ => num_cvars Gamma
    | ext_cvar Gamma _ => 1 + num_cvars Gamma
  end.

Lemma cvar_index_bound : forall Gamma x U V,
  get_cvar Gamma x = Some (U, V) ->
  x < num_cvars Gamma.
Proof.
  intros. generalize dependent x. generalize dependent U; generalize dependent V.
  induction Gamma; intros.
    inversion H.
    simpl. simpl in H. destruct (get_cvar Gamma x) eqn:Hx.
      destruct p. eapply IHGamma. eassumption. inversion H.
    simpl. simpl in H. destruct (get_cvar Gamma x) eqn:Hx.
      destruct p. eapply IHGamma. eassumption. inversion H.
    simpl. simpl in H. destruct x.
      omega.
      assert (x < num_cvars Gamma -> S x < S (num_cvars Gamma)) by omega.
      apply H0. eapply IHGamma. eassumption.
Qed. 


Lemma no_cvars_cshift_ind : forall Gamma c U V n,
  Gamma |- c ; U ~~ V ->
  num_cvars Gamma = n ->
  cshift n c = c.
Proof with eauto.
  intros. coercion_cases (induction H) Case; simpl;
  try (rewrite IHwell_formed_coercion);
  try (rewrite IHwell_formed_coercion1);
  try (rewrite IHwell_formed_coercion2);
  try (rewrite IHwell_formed_coercion3)...
  Case "C_Var".
    assert (x < num_cvars Gamma). eapply cvar_index_bound. eassumption.
    simpl. destruct le_gt_dec. 
      omega. trivial.
Qed.


Lemma no_cvars_shift_cn_ind : forall Gamma t T n,
  Gamma |- t \in T    ->
  num_cvars Gamma = n ->
  shift_cn n t = t.
Proof with eauto.
  intros; generalize dependent n; has_type_cases (induction H) Case;
  intros; simpl;
  try (rewrite IHhas_type); try (rewrite IHhas_type1); try (rewrite IHhas_type2);
  try (erewrite no_cvars_cshift_ind; trivial; eassumption; trivial)...
  Case "T_CAbs".
    simpl. omega.
Qed.



(* ####################################################### *)  
(** ** Context manipulation with term variables.           *)
(* ####################################################### *)

(* Term variables can be strengthened in type, context and 
   coercion judgments, and can be weakened in all judgements. 
 *)


Fixpoint remove_var (Gamma : context) (x : nat) : context :=
  match Gamma with
  | empty       => empty
  | ext_tvar Gamma' k => ext_tvar (remove_var Gamma' x) k
  | ext_var Gamma' T =>
    match x with
      | O   => Gamma'
      | S y => ext_var (remove_var Gamma' y) T
    end
  | ext_cvar Gamma' (U, V) =>
    ext_cvar (remove_var Gamma' x) (U, V)
  end.


Lemma remove_preserves_get : forall Gamma x n,
  get_tvar Gamma n = get_tvar (remove_var Gamma x) n.
Proof.
  induction Gamma; intros. simpl. trivial.
  induction x; intros. trivial.
    induction n. simpl. trivial.
    simpl. trivial.
  simpl. destruct n. trivial. trivial.
  simpl. destruct p. simpl. trivial.
Qed.

Lemma remove_var_get_cvar : forall Gamma x y,
  get_cvar Gamma x = get_cvar (remove_var Gamma y) x.
Proof.
  induction Gamma; intros; try (destruct x); try(destruct p); try (destruct y);
  simpl; try (apply f_equal); simpl; trivial.
Qed.


(* --- term variable strengthening --- *)

Lemma type_remove_var : forall Gamma x T k,
  well_formed_type Gamma T k ->
  well_formed_type (remove_var Gamma x) T k. 
Proof.
  intros. generalize dependent Gamma. generalize dependent k.
  induction T; intros; inversion H; try constructor.
    rewrite <- remove_preserves_get. trivial.
    trivial.
    apply WF_TApp with k'. subst.
    apply IHT1. trivial. apply IHT2. trivial.
    subst.
    apply IHT in H3. simpl in H3. trivial.
Qed.  

Lemma context_remove_var : forall Gamma x,
  well_formed_context Gamma ->
  well_formed_context (remove_var Gamma x).
Proof.
  intros. generalize dependent x. induction Gamma; intro x.
    simpl. trivial.
    simpl. destruct x.
      inversion H; trivial.
      constructor. inversion H; subst. apply type_remove_var.
      trivial.
    apply IHGamma. inversion H. trivial.
    simpl. constructor. apply IHGamma. inversion H. trivial.
    simpl. destruct p. inversion H. apply WFC_ext_cvar with k.
      apply IHGamma. trivial.
      apply type_remove_var. trivial.
      apply type_remove_var. trivial.
Qed.

Lemma coercion_remove_var : forall Gamma c x U V,
  Gamma |- c ; U ~~ V ->
  remove_var Gamma x |- c; U ~~ V.
Proof.
  coercion_cases (induction 1) Case; intros;
  try (econstructor; eauto);
  try (apply context_remove_var; trivial);
  try (apply type_remove_var; eauto).
  - rewrite <- remove_var_get_cvar with (y := x). trivial.
Qed.


Lemma type_strengthening_var : forall Gamma U T k,
   well_formed_type (ext_var Gamma U) T k ->
   well_formed_type Gamma T k.
Proof.
  intros. eapply type_remove_var with (x := 0) in H.
  simpl in H. trivial.
Qed.

Lemma coercion_strengthening_var :
  forall Gamma c U V W,
    ext_var Gamma U |- c ; V ~~ W ->
                           Gamma |- c ; V ~~ W.
Proof.
  intros. eapply coercion_remove_var with (x:= 0) in H.
  simpl in H. trivial.
Qed.
                                     
(* ------- term variable weakening ----------------------- *)


Lemma get_var_remove_lt : forall Gamma x y,
  x < y -> get_var (remove_var Gamma y) x = get_var Gamma x.
Proof.
  intros. generalize dependent x. generalize dependent y.
  induction Gamma; intros.
    trivial.
    simpl. destruct y.
      omega.
      destruct x.
        trivial.
        apply IHGamma. omega.
    simpl. apply f_equal. apply IHGamma. trivial.
    simpl. destruct p. erewrite <- IHGamma. simpl. reflexivity. trivial.
Qed.

Lemma get_var_remove_ge : forall Gamma x y,
  x >= y -> get_var (remove_var Gamma y) x = get_var Gamma (S x).
Proof.
  intros. generalize dependent x. generalize dependent y.
  induction Gamma; intros.
    trivial.
    simpl. destruct y.
      trivial.
      destruct x.
        omega.
        apply IHGamma. omega.
    simpl. apply f_equal. apply IHGamma. trivial.
    simpl. destruct p. simpl. apply IHGamma. trivial.
Qed.

Lemma wf_type_insert_var :
  forall Gamma n T k,
  well_formed_type (remove_var Gamma n) T k ->
  well_formed_type Gamma T k.
Proof.
  intros Gamma n T k H.
  remember (remove_var Gamma n) as G.
  revert HeqG. generalize Gamma.
  generalize dependent G.
  induction 1; intros; subst; econstructor; eauto.
  - rewrite <- remove_preserves_get in H. auto.
Qed.

Lemma wf_weakening_var : forall Gamma U T k,
  well_formed_type Gamma U k ->
  well_formed_type (ext_var Gamma T) U k.
Proof.  
  intros. eapply wf_type_insert_var with 0. simpl. auto.
Qed.


Lemma coercion_weakening_var : forall Gamma c x U V,
  well_formed_context Gamma ->
  remove_var Gamma x |- c ; U ~~ V ->
  Gamma |- c; U ~~ V.
Proof with eauto.
  intros; remember (remove_var Gamma x) as G; generalize dependent Gamma;
  coercion_cases (induction H0) Case; intros; subst; try constructor;
  try (eapply C_Trans; eauto);
  try (eapply C_Refl; eauto);
  try (eapply C_App; eauto);
  try (eapply C_ALeft; eauto);
  try (eapply C_ARight; eauto);
  try (eapply C_Inst; eauto);
  trivial;
  try (eapply wf_type_insert_var; eauto);
  try (apply IHwell_formed_coercion; trivial; trivial);
  try (apply IHwell_formed_coercion1; trivial; trivial);
  try (apply IHwell_formed_coercion2; trivial; trivial);
  try (apply IHwell_formed_coercion3; trivial; trivial);
  try (constructor; trivial).
  Case "C_Var".
  erewrite remove_var_get_cvar. eassumption.
Qed.


Lemma typing_weakening_var_ind : forall Gamma n t U,
  well_formed_context Gamma ->
  remove_var Gamma n |- t \in U ->
  Gamma |- shift n t \in U.
Proof.
  intros. generalize dependent U. 
  generalize dependent Gamma. generalize dependent n.
  t_cases (induction t) Case; intros;
  inversion H0; subst.
  Case "tvar".
  constructor. trivial.
    destruct (le_gt_dec n0 n);
      rewrite <- H4; symmetry. apply get_var_remove_ge. omega.
      apply get_var_remove_lt. omega.
  Case "tapp".
    simpl. eapply T_App. apply IHt1. trivial. apply H4.
    apply IHt2. trivial. trivial.
  Case "tabs".
  simpl. constructor.
  eapply wf_type_insert_var; eauto. 
  apply IHt. constructor. 
  eapply wf_type_insert_var; eauto.
  auto. simpl. auto.
  Case "ttapp".
    simpl. econstructor; eauto. 
    eapply wf_type_insert_var; eauto. 
  Case "ttabs".
    simpl. constructor. apply IHt. constructor. trivial.
    simpl. trivial.
  Case "tcapp".
    simpl. econstructor. apply IHt. trivial. eassumption.
    eapply coercion_weakening_var. trivial. eassumption.
  Case "tcabs".
    simpl. constructor. apply IHt. econstructor; trivial.
    eapply wf_type_insert_var. eassumption.
    eapply wf_type_insert_var. eassumption.
    simpl. trivial.
    eapply wf_type_insert_var. eassumption.
    eapply wf_type_insert_var. eassumption.
  Case "tcoerce".
    simpl. econstructor. eapply coercion_weakening_var. trivial.
    eassumption.
    apply IHt. trivial. trivial.
Qed.

Lemma typing_weakening_var : forall Gamma t U V,
  well_formed_context Gamma ->                               
  well_formed_type Gamma V KStar ->
  Gamma |- t \in U         ->
  ext_var Gamma V |- shift 0 t \in U.
Proof.
  intros. eapply typing_weakening_var_ind. constructor; trivial. 
  simpl. trivial.
Qed.

(* -------------- weakening without shifting ------------- *)

Fixpoint num_vars (Gamma:context) : nat :=
  match Gamma with
    | empty => 0
    | ext_var Gamma _ => 1 + num_vars Gamma
    | ext_tvar Gamma k => num_vars Gamma
    | ext_cvar Gamma _ => num_vars Gamma
  end.

Lemma var_index_bound : forall Gamma x T,
  get_var Gamma x = Some T ->
  x < num_vars Gamma.
Proof.
  intros. generalize dependent x. generalize dependent T.
  induction Gamma; intros.
    inversion H.
    simpl. simpl in H. destruct x.
      omega.
      assert (x < num_vars Gamma -> S x < S (num_vars Gamma)) by omega.
      apply H0. eapply IHGamma. eassumption.
    simpl. simpl in H. destruct (get_var Gamma x) eqn:Hx.
      eapply IHGamma. eassumption. inversion H.
    simpl. simpl in H. destruct (get_var Gamma x) eqn:Hx.
      eapply IHGamma. eassumption. inversion H.
Qed. 



Lemma no_vars_shift_ind : forall Gamma t T n,
  Gamma |- t \in T ->
  num_vars Gamma = n ->
  shift n t = t.
Proof.
  intros. generalize dependent T. generalize dependent n.
  generalize dependent Gamma.
  t_cases (induction t) Case; intros; inversion H; subst.
  Case "tvar".
    remember (num_vars Gamma) as m. assert (n < num_vars Gamma).
    eapply var_index_bound. eassumption. simpl.
    destruct le_gt_dec. omega. trivial.
  Case "tapp".
    simpl. erewrite IHt1. erewrite IHt2. trivial. reflexivity.
    eassumption. reflexivity. eassumption.
  Case "tabs".
    simpl. erewrite (IHt (ext_var Gamma t)). trivial. trivial.
    eassumption.
  Case "ttapp".
    simpl. erewrite IHt. trivial. reflexivity. eassumption.
  Case "ttabs".
    simpl. erewrite (IHt (ext_tvar Gamma k)); trivial. eassumption.
  Case "tcapp".
    simpl. erewrite IHt. trivial. reflexivity. eassumption.
  Case "tcabs".
    simpl. erewrite (IHt (ext_cvar Gamma (t, t0))). trivial. trivial.
    eassumption.
  Case "tcoerce".
    simpl. erewrite IHt. trivial. reflexivity. eassumption.
Qed.

Lemma no_vars_shift : forall t T,
  empty |- t \in T ->
  shift 0 t = t.
Proof.
  intros. eapply no_vars_shift_ind. eassumption. trivial.
Qed.


(* ####################################################### *)  
(** ** Context manipulation with all variables.            *)
(* ####################################################### *)

