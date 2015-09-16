Require Import Omega.

Require Export SFC.Typing.
Require Import SFC.Weakening.
Require Import SFC.SystemFC.
Require Import SFC.Shifting.
Require Import SFC.Substitution.
Require Export Coq.Logic.Decidable.


(* ####################################################### *)  
(* ** Substitution for type variables.                     *)
(* ####################################################### *)  

(* Substitute for the nth type variable in the context. *)
Inductive subst_context :
  ty -> kind -> nat -> context -> context -> Prop := 
  | s_ext_var : forall T k n Gamma Gamma' U U',
      subst_context T k n Gamma Gamma' ->
      [n := T] U = U' ->
      subst_context T k n (ext_var Gamma U) (ext_var Gamma' U')
  | s_ext_tvar0 : forall T Gamma k,
      (* the variable is removed because it has been replaced *)
      well_formed_type Gamma T k ->
      well_formed_context Gamma ->
      subst_context T k 0 (ext_tvar Gamma k) Gamma
  | s_ext_tvar : forall T k n Gamma Gamma' k',
      subst_context T k n Gamma Gamma' ->
      subst_context (tshift 0 T) k (S n)
                    (ext_tvar Gamma k') (ext_tvar Gamma' k')
  | s_ext_cvar : forall T k U1 V1 U2 V2 n Gamma Gamma',
      subst_context T k n Gamma Gamma' ->
      [n := T] U1 = U2   ->
      [n := T] V1 = V2   ->
      subst_context T k n (ext_cvar Gamma (U1, V1)) (ext_cvar Gamma' (U2, V2)).

Hint Constructors subst_context.
Lemma context_subst_eq : forall X Gamma Gamma' T k,
 subst_context T k X Gamma Gamma' ->                           
 get_tvar Gamma X = Some k.
Proof.
  intros. induction H; intros; simpl; auto.
Qed.

Lemma context_subst_ge : forall Gamma Gamma' X X' T k,
  X' < X ->
  subst_context T k X' Gamma Gamma' ->
  get_tvar Gamma' (X - 1) = get_tvar Gamma X. 
Proof.
  intros. generalize dependent X. induction H0; intros.
    simpl. apply IHsubst_context. trivial.
    induction X. inversion H1.
      simpl. assert (X - 0 = X) by omega. rewrite H2.
      trivial.
    inversion H; subst. simpl. 
    assert (get_tvar Gamma' (S n - 1) = get_tvar Gamma (S n)).
      apply IHsubst_context. omega.
    assert (S n - 1 = n) by omega. rewrite H2 in H1.
    trivial.
    simpl. destruct m. inversion H1.
    simpl. assert (get_tvar Gamma' (S m - 1) = get_tvar Gamma (S m)).
      apply IHsubst_context. omega. assert (S m - 1 = m) by omega.
      rewrite H3 in H2. trivial.
    simpl. apply IHsubst_context. trivial.
Qed.

Lemma context_subst_lt : forall Gamma Gamma' X X' T k,
  X' > X ->
  subst_context T k X' Gamma Gamma' ->
  get_tvar Gamma' X = get_tvar Gamma X. 
Proof.
  intros. generalize dependent X. induction H0; intros.
    simpl. apply IHsubst_context. trivial.
    inversion H1.
    induction X. simpl. trivial.
    simpl. apply IHsubst_context. omega.
    simpl. apply IHsubst_context. omega.
Qed.

Lemma subst_context_var : forall Gamma Gamma' U k X x,
  subst_context U k X Gamma Gamma' ->
  get_var Gamma x = None         ->
  get_var Gamma' x = None.
Proof.
  intros. generalize dependent x. induction H; intros.
    simpl. destruct x.
      subst. inversion H1.
      apply IHsubst_context. inversion H1. trivial.
    simpl in H1. unfold opt_map in H1. destruct (get_var Gamma x).
      inversion H1. trivial.
    simpl. rewrite IHsubst_context. trivial. simpl in H0.
      destruct (get_var Gamma x). inversion H0. trivial.
    simpl. simpl in H2. apply IHsubst_context. trivial.
Qed.

Lemma context_subst_wf : forall Gamma Gamma' X U k,
   subst_context U k X Gamma Gamma'  ->
   well_formed_type Gamma' U k.
 Proof with auto.
   intros Gamma Gamma' X U k Hs. induction Hs; intros.
   - apply wf_weakening_var; auto.
   - trivial.
   - apply type_weakening_tvar. trivial.
   - apply type_weakening_cvar. trivial.
Qed.

Lemma subst_preserves_well_formed_type : forall T X Gamma Gamma' U k k',
   subst_context U k X Gamma Gamma'    ->
   well_formed_type Gamma T  k'      ->
   well_formed_type Gamma' ([X := U] T) k'.
 Proof.
   intro T. 
   induction T; intros.
   Case "TVar". simpl.
     destruct (eq_nat_dec X n).
     SCase "X = n". subst.
     inversion H0. rewrite context_subst_eq with
                           (Gamma' := Gamma')
                             (T := U) (k := k) in H2. inversion H2.
       subst.
       eapply context_subst_wf. eapply H. trivial.
     SCase "X <> n".
       destruct (le_lt_dec X n).
       SSCase "X < n". constructor.
         inversion H0. rewrite <- H2.
         apply context_subst_ge with X U k.
         omega. trivial.
       SSCase "X > n".
          constructor. inversion H0. rewrite <- H2.
       apply context_subst_lt with X U k.
         omega. trivial.
   Case "TCon".           
       simpl. constructor. inversion H0. trivial.
   Case "TApp". 
     inversion H0. simpl. apply WF_TApp with k'0. eapply IHT1; eauto.
     eapply IHT2; eauto.
     Case "TUniv".
     inversion H0. subst.
     simpl. constructor. eapply IHT.
     assert (K: X + 1 = S X) by omega. rewrite K.
     constructor. apply H. trivial.
 Qed.

 

 Lemma subst_context_wf : forall Gamma Gamma' X U k,
   subst_context U k X Gamma Gamma' ->
   well_formed_context Gamma      ->
   well_formed_context Gamma'.
 Proof.
   intros Gamma Gamma' X U k H. induction H; intros.
   - inversion H1.
     constructor. rewrite <- H0.
     apply subst_preserves_well_formed_type with Gamma k. auto. auto. auto.
   -  auto.
   - constructor. apply IHsubst_context. inversion H0. trivial.
   - inversion H2. econstructor; eauto. rewrite <- H0.
     apply subst_preserves_well_formed_type with Gamma k. auto. eauto.
     rewrite <- H1.
     apply subst_preserves_well_formed_type with Gamma k. auto. eauto.
Qed.

 (*
 Lemma tshift_subst_prop : forall X Y T U,
   tshift X ([X + Y := U] T) =
   [S (X + Y) := tshift X U] (tshift X T).
 Proof.
   intros. generalize dependent U. common_cases X T. intros.
   simpl. destruct (eq_nat_dec (n'' + Y) n). simpl. trivial.
   destruct (le_lt_dec (n'' + Y) n). simpl.
   destruct (le_gt_dec n'' (n - 1)). assert (S (n - 1) = n - 0) by omega.
     rewrite H. trivial. omega. 
     simpl. destruct (le_gt_dec n'' n). trivial. omega.
   intros. destruct (eq_nat_dec (n'' + Y) n). omega.
     destruct (le_lt_dec (n'' + Y) n). omega.
     simpl. destruct (le_gt_dec n'' n). omega.
     destruct
       (match n as n1 return ({S (n'' + Y) = n1} + {S (n'' + Y) <> n1}) with
          | 0 => right (not_eq_sym (O_S (n'' + Y)))                           
          | S m =>                                                     
            sumbool_rec                                                     
              (fun _ : {n'' + Y = m} + {n'' + Y <> m} =>                    
                 {S (n'' + Y) = S m} + {S (n'' + Y) <> S m})                  
              (fun a : n'' + Y = m => left (f_equal S a))                   
              (fun b : n'' + Y <> m => right (not_eq_S (n'' + Y) m b))      
              (eq_nat_dec (n'' + Y) m)                                      
        end). omega. 
     destruct (le_gt_dec (S (n'' + Y)) n). omega.
     destruct n. trivial. simpl. unfold sumbool_rec. unfold sumbool_rect.
     destruct (le_lt_dec (n'' + Y) n). omega.
    
     admit.
(*     trivial.  *)
     apply f_equal. 
     assert (n'' + Y + 1 = S n'' + Y) by omega. rewrite H.
     assert (tshift 0 (tshift (0 + n'') U) = tshift (1 + 0 + n'') (tshift 0 U))
       by (apply tshift_tshift_prop).
     simpl in H0. rewrite H0. 
     rewrite IHT. trivial. 
(*     rewrite IHT1. rewrite IHT2. rewrite IHT3. trivial. *)
 Qed.
*)
 
Lemma context_subst_get_cvar : forall X Y Gamma Gamma' U k,
  subst_context U k Y Gamma Gamma' ->
  get_cvar Gamma' X = opt_map_prod (fun T => [Y := U] T) (get_cvar Gamma X).
Proof.
   intros. generalize dependent X. induction H; intros. 
   Case "ext_var".  
     simpl. apply IHsubst_context.
   Case "ext_tvar".
     simpl. induction (get_cvar Gamma X).
       simpl. destruct a. simpl. apply f_equal.
       assert (t = subst_type_in_type_fix 0 T (tshift 0 t)) by
           (apply subst_shift_same). rewrite <- H1; clear H1.
       assert (t0 = subst_type_in_type_fix 0 T (tshift 0 t0)) by
           (apply subst_shift_same). rewrite <- H1; clear H1.
       trivial.
       simpl. trivial.
       simpl. rewrite IHsubst_context. induction (get_cvar Gamma X).
         simpl. assert (S n = S (0 + n)) by omega. rewrite H0. destruct a.
         simpl. 
         assert (forall t, subst_type_in_type_fix n T t = [0 + n := T] t) by trivial.
         rewrite H1. rewrite tshift_subst_prop. trivial. rewrite H1.
         rewrite tshift_subst_prop. trivial.
         simpl. trivial.     
     Case "ext_cvar".
       simpl. destruct X.
         simpl. rewrite <- H0.
         rewrite <- H1.
         trivial.
       apply IHsubst_context.
 Qed.
 
Lemma subst_typ_preserves_coercion_ind : forall Gamma Gamma' c U1 U2 V k X,
  subst_context V k X Gamma Gamma' ->                                        
  Gamma  |- c ; U1 ~~ U2          ->
  Gamma' |- [X := V] c ; [X := V] U1 ~~ [X := V] U2.
Proof with eauto.
  intros; generalize dependent Gamma'; generalize dependent X;
  generalize dependent V; coercion_cases (induction H0) Case; intros;
  simpl; try constructor; try (eapply C_Trans); try (eapply C_App; eauto);
  try (eapply subst_context_wf; eassumption; trivial);
  try (apply IHwell_formed_coercion; trivial);
  try (apply IHwell_formed_coercion1; trivial);
  try (apply IHwell_formed_coercion2; trivial);
  try (apply IHwell_formed_coercion3; trivial).
  Case "C_Var".
    erewrite context_subst_get_cvar with (Gamma:=Gamma). erewrite H0.
    simpl. trivial. eauto.
  Case "C_Refl".
    econstructor. eapply subst_context_wf. eauto. trivial.
    eapply subst_preserves_well_formed_type. eassumption. eassumption.
  Case "C_App".
  inversion H. subst.
  econstructor.
  eapply subst_preserves_well_formed_type; eauto.
  eapply subst_preserves_well_formed_type; eauto.
  inversion H0. subst.
  econstructor.
  eapply subst_preserves_well_formed_type; eauto.
  eapply subst_preserves_well_formed_type; eauto.
  Case "C_Forall".
    assert (X + 1 = S X) by omega. rewrite H3. apply IHwell_formed_coercion.
    constructor. trivial.
    inversion H. subst.
    econstructor.
    eapply subst_preserves_well_formed_type; eauto.
    assert (X + 1 = S X) by omega. rewrite H3.
    econstructor. eauto.
    inversion H1. subst. econstructor.
    eapply subst_preserves_well_formed_type; eauto.
    assert (X + 1 = S X) by omega. rewrite H3.
    econstructor. eauto.
  Case "C_ALeft"; eapply C_ALeft.
  inversion H. subst. eapply subst_preserves_well_formed_type; eauto.
  inversion H0. subst. eapply subst_preserves_well_formed_type; eauto.
  simpl. subst. econstructor. eauto.
  simpl. subst. econstructor. eauto.
  simpl. econstructor. eapply subst_preserves_well_formed_type; eauto.
  eapply subst_preserves_well_formed_type; eauto.
  eapply subst_preserves_well_formed_type; eauto.
  eapply IHwell_formed_coercion; eauto.
  Case "C_ARight"; eapply C_ARight.
  inversion H. subst. eapply subst_preserves_well_formed_type; eauto.
  inversion H0. subst. eapply subst_preserves_well_formed_type; eauto.
  simpl. subst. econstructor. eauto.
  simpl. subst. econstructor. eauto.
  simpl. subst. econstructor. eauto.
  simpl. subst. econstructor. eauto.
  eapply subst_preserves_well_formed_type; eauto.
  eapply subst_preserves_well_formed_type; eauto.
  eapply subst_preserves_well_formed_type; eauto.
  econstructor. eauto.
  eapply subst_preserves_well_formed_type; eauto.
  eapply IHwell_formed_coercion; eauto.
  Case "C_Inst".
  assert (X = 0 + X) by trivial. rewrite H2.
    rewrite tsubst_tsubst_prop. 
    rewrite tsubst_tsubst_prop. econstructor.
    simpl in IHwell_formed_coercion. simpl.
    assert (S X = X + 1) by omega. rewrite H3.
    apply IHwell_formed_coercion. trivial. eapply subst_preserves_well_formed_type.
    simpl. eassumption. trivial. 
Qed.

 Lemma context_subst_get_var : forall X Y Gamma Gamma' U k,
  subst_context U k Y Gamma Gamma' ->
  get_var Gamma' X = opt_map (fun T => [Y := U] T) (get_var Gamma X).
Proof.
   intros. generalize dependent X. induction H; intros. 
     simpl. destruct X.
       simpl. rewrite <- H0.
       trivial.
       apply IHsubst_context.
     simpl. induction (get_var Gamma X).
       simpl. apply f_equal. apply subst_shift_same. trivial.
     simpl. rewrite IHsubst_context. induction (get_var Gamma X).
       simpl. apply f_equal. assert (S n = S (0 + n)) by omega. rewrite H0.
       assert (subst_type_in_type_fix n T a = [0 + n := T] a) by trivial.
       rewrite H1. apply tshift_subst_prop. trivial.
     simpl. apply IHsubst_context.
 Qed.


Lemma subst_typ_preserves_typing_ind : forall Gamma Gamma' t U V k X,
  subst_context V k X Gamma Gamma' ->
  Gamma |- t \in U               ->
  Gamma' |- [X := V]t \in [X := V]U.
Proof.
  intros. generalize dependent Gamma'. generalize dependent X. 
  generalize dependent V.
  has_type_cases (induction H0) Case; intros.
  Case "T_Var".
    constructor. eapply subst_context_wf. apply H1. trivial.
    simpl. erewrite context_subst_get_var with (Gamma:=Gamma).
    erewrite H0.
    simpl. eauto. eauto.
  Case "T_Abs".
  simpl. constructor.
  eapply subst_preserves_well_formed_type; eauto.
  apply IHhas_type. constructor. trivial. trivial.
  Case "T_App".
    simpl. econstructor. apply IHhas_type1. trivial. apply IHhas_type2. trivial.
  Case "T_TAbs".
    simpl. constructor. apply IHhas_type.
    assert (X + 1 = S X) by omega. rewrite H1. clear H1.
    constructor. trivial.
  Case "T_TApp".
    simpl. assert (X = 0 + X) by trivial. rewrite H3. clear H3. 
    rewrite tsubst_tsubst_prop. simpl. econstructor. 
    assert (S X = X + 1) by omega.  rewrite H3. clear H3. 
    apply IHhas_type. trivial. eapply subst_preserves_well_formed_type. apply H2.
    trivial. eapply subst_context_wf. apply H2. trivial.
  Case "T_CAbs".
    simpl. constructor. apply IHhas_type. constructor. trivial.
    trivial.
    trivial.
    eapply subst_preserves_well_formed_type. eassumption.
    trivial. eapply subst_preserves_well_formed_type. eassumption. trivial.
  Case "T_CApp".    
    simpl. econstructor. simpl in IHhas_type.  apply IHhas_type. trivial.
    eapply subst_typ_preserves_coercion_ind. eassumption. trivial.
  Case "T_Coerce".
    simpl. econstructor.
    eapply subst_typ_preserves_coercion_ind. eassumption. eassumption.
    apply IHhas_type. trivial.
Qed.

Lemma subst_typ_preserves_typing : forall Gamma t U V k,
  well_formed_context Gamma ->                                     
  well_formed_type Gamma V k  ->
  ext_tvar Gamma k |- t \in U ->
  Gamma |- [0 := V]t \in [0 := V]U.
Proof.
  intros. eapply subst_typ_preserves_typing_ind. constructor.
  trivial. eauto. eauto. eauto.
Qed.



(* ####################################################### *)  
(** ** Regularity properties                               *)
(* ####################################################### *)

Lemma coercion_context : forall Gamma c U V,
                           Gamma |- c ; U ~~ V -> well_formed_context Gamma.
Proof.
  induction 1; eauto. inversion IHwell_formed_coercion; auto.
Qed.

Lemma term_context : forall Gamma t T,
                     Gamma |- t \in T -> well_formed_context Gamma.
Proof.
  induction 1; try (inversion IHhas_type; eauto; econstructor); eauto.
Qed.
                                        

Lemma type_in_context_wf_coercion : forall Gamma n U V,
  well_formed_context Gamma      ->
  get_cvar Gamma n = Some (U, V) ->
  exists k, well_formed_type Gamma U k /\ well_formed_type Gamma V k.
Proof.
  induction Gamma; intros.
  Case "empty".
    inversion H0.
  Case "ext_var".
  assert (K: exists k,
            well_formed_type Gamma U k /\ well_formed_type Gamma V k).
      SCase "Pf of assertion".
      eapply IHGamma. inversion H. trivial. eassumption.
    destruct K as [ k [ WF1 WF2]]. exists k.
    split; apply wf_weakening_var; trivial. 
  Case "ext_tvar".
    simpl in H0. destruct (get_cvar Gamma n) eqn:Heq; inversion H0; subst.
      destruct p.
      assert (K : exists k,
                well_formed_type Gamma t k /\ well_formed_type Gamma t0 k).
      SSCase "Pf of assertion".
      eapply IHGamma; inversion H; trivial; eassumption.
      destruct K as [ k' [WF1 WF2]]. exists k'.
      inversion H2. subst. split; apply type_weakening_tvar; trivial.
  Case "ext_cvar".
    destruct p; inversion H; subst; destruct n.
    SCase "n = 0".
    exists k. split; eapply type_weakening_cvar;
              inversion H0; subst; trivial.
    SCase "n = S n".
      assert (exists k, well_formed_type Gamma U k /\ well_formed_type Gamma V k).
      SSCase "Pf of assertion".
        eapply IHGamma. trivial. eassumption.
      destruct H1 as [k' [Hu Hv]]. exists k'.
        split; apply type_weakening_cvar; trivial. 
Qed.      

    
Lemma type_in_context_wf : forall x T Gamma,
  well_formed_context Gamma ->
  get_var Gamma x = Some T  ->
  well_formed_type Gamma T KStar.
Proof.
  intros. generalize dependent T. generalize dependent x.
  induction Gamma; intros. 
    inversion H0.
    inversion H0; subst. destruct x.
    apply wf_weakening_var. inversion H; subst. inversion H2; subst.
      trivial.
      apply wf_weakening_var. eapply IHGamma. inversion H; subst. trivial.
      apply H2.
    
    simpl in H0. unfold opt_map in H0. destruct (get_var Gamma x) eqn:Hg.
    inversion H0; subst. apply type_weakening_tvar. eapply IHGamma.
    inversion H.
    trivial. apply Hg.
    inversion H0.
    destruct p. apply type_weakening_cvar. eapply IHGamma. inversion H.
    trivial. simpl in H0. eassumption.
Qed.

Lemma coercion_well_formed : forall Gamma c U V,
  (Gamma |- c ; U ~~ V) ->
  well_formed_context Gamma /\
  exists k,
    well_formed_type Gamma U k /\ well_formed_type Gamma V k.
Proof.
  intros; coercion_cases (induction H) Case; intros;
  try (destruct IHwell_formed_coercion as [Ih0 [k0 [HT01 HT02]]]);
  try (destruct IHwell_formed_coercion1 as [Ih1 [k1 [HT11 HT12]]]);
  try (destruct IHwell_formed_coercion2 as [Ih2 [k2 [HT21 HT22]]]);
  try (split; eauto).

  Case "C_Var".
  eapply type_in_context_wf_coercion; eauto.
  Case "C_Trans".
  assert (k1 = k2). eapply kinds_unique; eauto.
  exists k1. subst. split; eauto. 
  Case "C_Forall".
  inversion Ih0. auto.
  Case "C_Inst".
  exists KStar.
  inversion HT01. inversion HT02. subst.
  split; apply subst_preserves_well_formed_type with (ext_tvar Gamma k) k; auto. 
Qed.


Lemma typing_well_formed : forall Gamma t U,
  Gamma |- t \in U ->
  (well_formed_type Gamma U KStar /\ well_formed_context Gamma).
Proof.
  intros. has_type_cases (induction H) Case;
    try (destruct IHhas_type);
    try (destruct IHhas_type1);
    try (destruct IHhas_type2);
    subst; split; eauto.
  Case "T_Var".
  eapply type_in_context_wf; eauto. 
  Case "T_Abs".
  eapply WF_TApp; eauto. eapply WF_TApp; eauto.
  constructor. eapply arrKind.
  apply type_strengthening_var with T11; auto.
  inversion H2. auto.
  Case "T_App".
  inversion H1. inversion H7. inversion H12.
  rewrite arrKind in H16. inversion H16. subst.
  auto.
  Case "T_TAbs".
  constructor. auto. inversion H1. auto.
  Case "T_TApp".
    inversion H2. subst.
    eapply subst_preserves_well_formed_type with (ext_tvar Gamma k) k. constructor. eauto. 
    trivial. auto.
  Case "T_CAbs".
    apply type_strengthening_remove_cvar with (X:=0) in H2. simpl in H2.
    econstructor; eauto. econstructor; eauto. econstructor; eauto.
    econstructor; eauto. apply coerceKind.
    apply term_context in H. inversion H. auto.
  Case "T_CApp".
  inversion H1. inversion H5. inversion H10. inversion H15. rewrite coerceKind in H19.
  inversion H19. subst. trivial.
  Case "T_Coerce".
  apply coercion_well_formed in H.
  destruct H as [K0 [k [K1 K2]]].
  assert (k = KStar). eapply kinds_unique with (U := T1) (k1 := k); auto. eauto. eauto. subst. auto.
Qed.


(* ####################################################### *)  
(** ** Substitution for coercion variables                 *)
(* ####################################################### *)  


Lemma cn_substitution_preserves_coercion : forall Gamma x c c' U1 U2 V1 V2,
  Gamma |- c ; U1 ~~ U2                ->
  remove_cvar Gamma x |- c' ; V1 ~~ V2 ->
  get_cvar Gamma x = Some (V1, V2)    ->
  remove_cvar Gamma x |- [x := c'] c ; U1 ~~ U2.
Proof.
  intros; generalize dependent x;  generalize dependent V1;
  generalize dependent V2; generalize dependent c';
  coercion_cases (induction H) Case; intros; simpl; try constructor;
  try (eapply C_Refl; eauto);
  try (eapply C_Trans); try (eapply C_App; eauto);
  try (eapply C_ALeft;eauto); try (eapply C_ARight; eauto);
  try (eapply C_Inst; eauto);
  try (eapply IHwell_formed_coercion; eassumption; trivial);
  try (eapply IHwell_formed_coercion1; eassumption; trivial);
  try (eapply IHwell_formed_coercion2; eassumption; trivial);
  try (eapply IHwell_formed_coercion3; eassumption; trivial);
  try (apply  context_strengthening_remove_cvar; trivial);
  try (eapply type_strengthening_remove_cvar; eauto);
  try (eapply type_strengthening_remove_cvar; eauto).

  Case "C_Var".
    destruct (eq_nat_dec x0 x).
    SCase "x = x0".
    subst. rewrite H0 in H2. inversion H2; subst. trivial.
    SCase "x <> x0".
      destruct le_lt_dec; constructor;
      try (apply context_strengthening_remove_cvar); trivial;
      rewrite <- H0; symmetry.
      SSCase "x0 <= x".
        assert (x = S (x-1)) by omega.
        rewrite H3. assert (S (x-1) - 1 = x - 1) by omega. rewrite H4.
        apply get_cvar_remove_ge. omega.
      SSCase "x < x0".
        apply get_cvar_remove_lt. trivial.
  Case "C_Forall".
    eapply IHwell_formed_coercion. simpl.
    apply coercion_well_formed in H. destruct H as [HG [k0 [HU HV]]].
    eapply coercion_weakening_tvar. eauto. 
    simpl. rewrite H3. simpl. auto.
Qed.


Lemma cn_substitution_preserves_typing : forall Gamma t c x U V T,
  Gamma |- t \in T                 ->
  remove_cvar Gamma x |- c ; U ~~ V ->
  get_cvar Gamma x = Some (U, V)   ->
  remove_cvar Gamma x |- [x:=c]t \in T.
Proof.
  intros Gamma t c; generalize dependent Gamma; generalize dependent c;
  t_cases (induction t) Case; intros; inversion H; subst;
  simpl; econstructor;
  try (eapply IHt; eassumption; eassumption; trivial);
  try (eapply IHt1; eassumption; eassumption; trivial);
  try (eapply IHt2; eassumption; eassumption; trivial);
  try (eapply cn_substitution_preserves_coercion; trivial; eassumption;
       trivial).
  Case "tvar".
  simpl.
    apply context_strengthening_remove_cvar. trivial.
    rewrite <- remove_cvar_get_var. trivial.
  Case "tabs".
    apply type_strengthening_remove_cvar. auto.
    assert (ext_var (remove_cvar Gamma x) t = remove_cvar (ext_var Gamma t) x)
      by trivial.
    rewrite H2. eapply IHt. trivial. simpl.
    eapply coercion_weakening_var with 0. constructor.
    apply type_strengthening_remove_cvar. auto.
    apply context_strengthening_remove_cvar.
    apply (term_context _ _ _ H). simpl. eauto. simpl. eauto.
    apply type_strengthening_remove_cvar. auto.
    apply context_strengthening_remove_cvar. auto.
(*  Case "ttapp".
    eapply type_strengthening_remove_cvar. trivial.
    apply wf_context_strengthening_cvar. trivial. *)
  Case "ttabs".
    assert (K: ext_tvar (remove_cvar Gamma x) k = remove_cvar (ext_tvar Gamma k) x) by
      trivial.
    rewrite K. eapply IHt.
      trivial.
      simpl. eapply coercion_weakening_tvar. eauto.
      simpl. rewrite H1. simpl. auto.
  Case "tcabs".
    assert (K: ext_cvar (remove_cvar Gamma x) (t, t0) =
            remove_cvar (ext_cvar Gamma (t, t0)) (S x)) by trivial.
    rewrite K. eapply IHt. trivial. simpl. eapply coercion_weakening.
    eapply context_strengthening_remove_cvar. eapply term_context. eauto.
    eauto.
    apply type_strengthening_remove_cvar. eauto.
    apply type_strengthening_remove_cvar. eauto. 
    simpl. eassumption.
    apply type_strengthening_remove_cvar. trivial.
    apply type_strengthening_remove_cvar. trivial.
Qed.





(* ####################################################### *)  
(** ** Substitution for term variables                 *)
(* ####################################################### *)  


Lemma substitution_preserves_typing_term_term : forall Gamma x U t v T,
     Gamma |- t \in T              ->
     remove_var Gamma x |- v \in U ->
     get_var Gamma x = Some U      ->
     remove_var Gamma x |- [x:=v]t \in T.
Proof with auto.
  intros Gamma x U t v T Ht Hv Hx.
  generalize dependent Gamma. generalize dependent T.
  generalize dependent U. generalize dependent v. generalize dependent x. 
  t_cases (induction t) Case; intros x v U T Gamma H Hv Hx;
    (* in each case, we'll want to get at the derivation of H *)
    inversion H; subst; simpl...
  Case "tvar".
    destruct (eq_nat_dec x n).
    SCase "x=n".
      subst. rewrite H3 in Hx. inversion Hx; subst. trivial.
    SCase "x<>n".
      destruct (le_lt_dec x n).
      SSCase "x <= n".
        apply T_Var. apply context_remove_var. trivial.
        assert (n = S (n - 1)) by omega. rewrite H0 in H3.
        rewrite <- H3. apply get_var_remove_ge. omega.
      SSCase "x > n".
        constructor. apply context_remove_var. trivial.
        rewrite <- H3. apply get_var_remove_lt. omega.
  Case "tapp".
    apply T_App with T11. apply IHt1 with U. trivial. trivial.
    trivial. apply IHt2 with U. trivial. trivial.
    trivial.
  Case "tabs".
    apply T_Abs.
    apply type_remove_var. auto.
    assert (K: ext_var (remove_var Gamma x) t =
                         remove_var (ext_var Gamma t) (S x)) by trivial.
    rewrite K. eapply IHt. trivial. simpl. apply typing_weakening_var.
    apply context_remove_var. eapply term_context. eauto.
    apply type_remove_var. trivial. eapply Hv. simpl. trivial.
  Case "ttapp".        
    econstructor. apply IHt with U. eauto.  eauto. trivial. 
    apply type_remove_var. trivial. apply context_remove_var.
    trivial.
  Case "ttabs".
    apply T_TAbs. assert (K : ext_tvar (remove_var Gamma x) k =
                         remove_var (ext_tvar Gamma k) x) by trivial.
    rewrite K. apply IHt with (tshift 0 U).
    trivial. rewrite <- K. apply term_weakening_tvar. trivial.
    simpl. rewrite Hx. trivial.
  Case "tcapp".
    econstructor. eapply IHt. eassumption. eassumption.
    trivial. eapply coercion_remove_var. trivial.
  Case "tcabs".
    constructor. assert (K: ext_cvar (remove_var Gamma x) (t, t0) =
                         remove_var (ext_cvar Gamma (t, t0)) x) by trivial.
    rewrite K. eapply IHt. trivial. 
    simpl. apply typing_weakening_cvar_ind. econstructor.
    apply typing_well_formed in H. inversion H. apply context_remove_var.
    trivial. apply type_remove_var; eauto. apply type_remove_var; trivial.
    simpl. eassumption. simpl. trivial. apply type_remove_var; trivial.
    apply type_remove_var; trivial.
  Case "tcoerce".
    econstructor. eapply coercion_remove_var.
    eassumption. eapply IHt. trivial. eassumption. trivial.
Qed.
