(** * SystemFCProp: Properties of System FC *)

Require Import Weakening.
Require Export SubstProp.
Require Export Evaluation.

Module SYSTEMFCPROP.
Import SYSTEMFC.
Import SHIFTING.
Import SUBSTITUTION.
Import TYPING.
Import EVALUATION.
Import WEAKENING.
Import SUBSTPROP.

Lemma tcon_injective :
  forall ts1 ts2 tc1 tc2,
    tcon tc1 ts1 = tcon tc2 ts2 -> tc1 = tc2 /\ ts1 = ts2.
Proof.
Admitted.
(*
  intros ts1.  induction ts1. induction ts2.
  - unfold tcon. simpl.  intros. inversion H. auto.
  - unfold tcon. simpl. intros. admit.
(*    
    destruct tcon_app with (tc := (TCon tc3)) (t := a) (ts := ts2) as [U [V EQ]].
    rewrite EQ in H0. simpl in H0. inversion H0.
    simpl in H0. simpl in IHts2.
  intros. destruct ts2. destruct tcon_app with (tc := (TCon tc1)) (t := a) (ts := ts1) as [U [V EQ]]. unfold tcon in H. simpl in *.
  rewrite EQ in H. inversion H.
*)
  - induction ts2. intros. admit.
    intros. unfold tcon in H. simpl in H.
*)  


(* ###################################################################### *)
(** * Inversion lemmas for the kinding relation. *)

Lemma arrow_kind_inv1 : forall Gamma t1 t2 k,
                          well_formed_type Gamma (tArrow t1 t2) k ->
                          well_formed_type Gamma t1 KStar.
Proof.
  intros.
  inversion H. inversion H2. inversion H7. rewrite arrKind in H11.
  inversion H11. subst. trivial.
Qed.

Lemma arrow_kind_inv2 : forall Gamma t1 t2 k,
                          well_formed_type Gamma (tArrow t1 t2) k ->
                          well_formed_type Gamma t2 KStar.
Proof.
  intros.
  inversion H. inversion H2. inversion H7. rewrite arrKind in H11.
  inversion H11. subst. trivial.
Qed.

Lemma arrow_kind_inv3 : forall Gamma t1 t2 k,
                          well_formed_type Gamma (tArrow t1 t2) k ->
                          k = KStar.
Proof.
  intros.
  inversion H. inversion H2. inversion H7. rewrite arrKind in H11.
  inversion H11. subst. trivial.
Qed.

(* ############################################################### *)

Fixpoint arg_kinds ks k :=
  match ks with
    | nil => k
    | k0 :: ks0 => KArrow k0 (arg_kinds ks0 k)
  end.


Inductive result_kind : kind -> kind -> Prop :=
| result_here : forall k k1, result_kind k (KArrow k1 k)
| result_next : forall k k1 k', result_kind k k' -> result_kind k (KArrow k1 k').

Fixpoint is_result (k : kind) (k2 : kind) : Prop :=
  match k2 with
    | KStar => False
    | KArrow k0 k1 => k = k1 \/ is_result k k1
  end.

(*
Lemma result_kind_antireflexive : forall k, ~(result_kind k k).
  unfold not. intro. induction k. intros. inversion H.
  intros.
Admitted.
 *)

Lemma kinds_oc : forall k k0, ~(k = KArrow k0 k).
  unfold not.
  intros. induction k. inversion H.
  inversion H. apply IHk2. auto.
Qed.

Lemma arg_kinds_oc : forall ks k1 k, k = KArrow k1 (arg_kinds ks k) -> False.
  induction k. intros. inversion H.
  intro H1. inversion H1.
Admitted.
(*
  destruct ks. simpl in H. inversion H. simpl in H.

  unfold not. simpl. inversion H.  inversion H. apply kinds_oc.
  unfold not in *. intros. simpl in H.
  destruct k. inversion H. inversion H.
  intros. unfold not. intros. inversion H.
  unfold not. intros. inversion H.
  destruct ks. simpl in H2. eapply kinds_oc. eauto.
  unfold not in IHk2. simpl in H2.
  apply IHk2 with (k0 := k) (ks := (k0 :: ks)). simpl. 
 *)

Lemma arg_kinds_inj1 : forall ks ks' k,
                         arg_kinds ks k = arg_kinds ks' k -> ks = ks'.
Proof.
  induction ks; intros. destruct ks'. trivial.
  simpl in H. inversion H. apply arg_kinds_oc in H. inversion H.
  destruct ks'. simpl in H. assert (k = (KArrow a (arg_kinds ks k))). auto.
    apply arg_kinds_oc in H0. inversion H0.
  simpl in H. inversion H. f_equal. apply IHks with k. trivial.
Qed.

Lemma tcon_app : forall ts t tc, exists u, exists v, tcon_aux tc (t :: ts) = TApp u v.
  intro ts. induction ts.
  intros. unfold tcon. simpl. exists tc. exists t. auto.
  intros t tc. simpl in IHts. simpl. apply IHts.  
Qed.

Inductive spine_similar : ty -> ty -> Prop :=
| similar_heads : forall tc1 tc2, spine_similar (TCon tc1) (TCon tc2)
| similar_apps  : forall t1 t2 u1 u2, spine_similar t1 t2 -> spine_similar (TApp t1 u1) (TApp t2 u2).                                          

Lemma tcon_aux_different : forall ts1 ts2 tc1 tc2, ~(tc1 = tc2) -> length ts1 = length ts2 -> ~(tcon_aux tc1 ts1 = tcon_aux tc2 ts2).
  induction ts1. unfold not. simpl. intros. destruct ts2. simpl in *. apply H. trivial. simpl in H0. inversion H0.
  unfold not in *. simpl in *. intros. destruct ts2. simpl in H0. inversion H0. simpl in H0. inversion H0. simpl in H1.
  apply (IHts1 ts2 (TApp tc1 a) (TApp tc2 t)). intro. inversion H2. apply H. trivial. trivial. trivial.
Qed.

(*
Lemma tcon_ts_different : forall ts1 ts2 tc, length ts1 <> length ts2 -> tcon tc ts1 <> tcon tc ts2.
  induction ts1. destruct ts2. auto. intro tc. simpl. unfold tcon. simpl.
Admitted.

Lemma tcon_inj1 : forall ts1 ts2 tc1 tc2, tcon tc1 ts1 = tcon tc2 ts2 -> tc1 = tc2.  
Admitted.
*)


Inductive well_formed_types Gamma : list ty -> list kind -> Prop :=
| wfts_nil : well_formed_types Gamma nil nil
| wfts_cons : forall t ts k ks, well_formed_type Gamma t k ->
                                well_formed_types Gamma ts ks ->
                                well_formed_types Gamma (t :: ts) (k :: ks).

Lemma tcon_types : forall Gamma ts ks t k,
  well_formed_type Gamma t (arg_kinds ks k) ->                    
  well_formed_types Gamma ts ks ->
  well_formed_type Gamma (tcon_aux t ts) k.
Proof.
  induction ts. intros.
  - destruct ks.
    simpl. simpl in H. trivial.
    simpl. inversion H0.
  - intros. destruct ks.
    inversion H0.
    inversion H0. subst.
    simpl. eapply IHts. econstructor. eauto. trivial. trivial.
Qed.

Lemma tcon_types_inv : forall Gamma ts t k,
  well_formed_type Gamma (tcon_aux t ts) k ->                         
  exists ks, well_formed_types Gamma ts ks /\ well_formed_type Gamma t (arg_kinds ks k).
Proof.
  induction ts; intros.
  - simpl in H. exists []. split. constructor. simpl. trivial.
  - simpl in H. destruct (IHts (TApp t a) k H) as [ks [HKS HT]].
    inversion HT.
    exists (k' :: ks). 
    split. constructor; trivial. simpl. trivial.
Qed.
                     

Lemma tcon_ind : forall Gamma ts tc ks,
   Sigma tc = Some (arg_kinds ks KStar) ->
   well_formed_type Gamma (tcon tc ts) KStar ->
   well_formed_types Gamma ts ks.
Proof.
  intros G ts tc ks EQ H.
  unfold tcon in H. destruct (tcon_types_inv G ts (TCon tc) KStar H) as [ks' [WFKS WFT]].
  inversion WFT. subst. rewrite EQ in H1. inversion H1.
  apply arg_kinds_inj1 in H2. subst. trivial.
Qed.
  
Lemma arrow_kind_inv4 : forall Gamma ts,
                          well_formed_type Gamma (tcon TArrow ts) KStar ->
                          exists t1 t2, ts = t1 :: t2 :: nil.
Proof.
  intros.
  assert (K : well_formed_types Gamma ts (KStar :: KStar :: nil)).
  apply tcon_ind with TArrow. simpl. apply arrKind. auto.
  inversion K. inversion H4. inversion H9. exists t. exists t0.  trivial.
Qed.

Lemma eq_kind_invs : forall Gamma k ts,
                       well_formed_type Gamma (tcon (TEq k) ts) KStar ->
                       exists t1 t2 t3, ts = t1 :: t2 :: t3 :: nil.
Proof.
  intros.
  assert (K : well_formed_types Gamma ts (k :: k :: KStar :: nil)).
  apply tcon_ind with (TEq k). simpl. apply coerceKind.
  auto. inversion K. inversion H4. inversion H9. inversion H14.
  eauto.
Qed.  



Lemma eq_kind_inv : forall Gamma k U V T k',
  well_formed_type Gamma (tCoerce k U V T) k' ->
  well_formed_type Gamma U k /\
  well_formed_type Gamma V k /\
  well_formed_type Gamma T KStar /\
  KStar = k'.          
Proof.
  intros. inversion H. inversion H2. inversion H7. inversion H12.
  rewrite coerceKind in H16. inversion H16. subst.
  split; auto; split; auto; split; auto.
Qed.


Lemma eq_kind_inv1 : forall Gamma k U V T k',
  well_formed_type Gamma (tCoerce k U V T) k' ->
  well_formed_type Gamma U k.
Proof.
  intros. inversion H. inversion H2. inversion H7. inversion H12.
  rewrite coerceKind in H16. inversion H16. subst. trivial.
Qed.

Lemma eq_kind_inv2 : forall Gamma k U V T k',
  well_formed_type Gamma (tCoerce k U V T) k' ->
  well_formed_type Gamma V k.
Proof.
  intros. inversion H. inversion H2. inversion H7. inversion H12.
  rewrite coerceKind in H16. inversion H16. subst. trivial.
Qed.

Lemma eq_kind_inv3 : forall Gamma k U V T k',
  well_formed_type Gamma (tCoerce k U V T) k' ->
  well_formed_type Gamma T KStar.
Proof.
  intros. inversion H. inversion H2. inversion H7. inversion H12.
  rewrite coerceKind in H16. inversion H16. subst. trivial.
Qed.

Lemma eq_kind_inv4 : forall Gamma k U V T k',
  well_formed_type Gamma (tCoerce k U V T) k' ->
  k' = KStar.
Proof.
  intros. inversion H. inversion H2. inversion H7. inversion H12.
  rewrite coerceKind in H16. inversion H16. subst. trivial.
Qed.

(* ###################################################################### *)

Inductive value_type : ty -> Prop :=
| v_univ : forall k T,
             value_type (TUniv k T)
| v_con  : forall tc ts t,
             t = tcon tc ts -> value_type t.


Inductive consistent_equality : ty -> ty -> Prop :=
| consistent_univ : forall k T1 T2,
     consistent_equality (TUniv k T1) (TUniv k T2)
| consistent_con  : forall tc ts1 ts2,
     consistent_equality (tcon tc ts1) (tcon tc ts2)
| consistent_l  : forall U V,
     ~(value_type V) -> consistent_equality U V
| consistent_r  : forall U V,
     ~(value_type U) -> consistent_equality U V.

(* We ASSUME that the context is consistent. *)
Parameter coercion_consistency : forall c U V,
   empty |- c ; U ~~ V ->
   consistent_equality U V.
  
Lemma coercion_consistency_arrow : forall c T U V,   
   empty |- c; T ~~ tArrow U V -> value_type T -> exists U1 V1, T = tArrow U1 V1.
Proof.
  intros c T U V HC HV.
  pose (K:= coercion_consistency _ _ _ HC). inversion K.
  - rewrite <- arrow_normalize in H1.
    destruct (coercion_well_formed _ _ _ _ HC) as [_ [k' [WFU WFV]]].
    assert (k' = KStar) by apply (arrow_kind_inv3 _ _ _ _ WFV). subst.
    apply tcon_injective in H1. destruct H1. subst.
    apply arrow_kind_inv4 in WFU. destruct WFU as [t1 [t2 EQ]]. subst.
    exists t1. exists t2. unfold tcon. simpl. trivial.
  - unfold not in H. assert False. apply H. rewrite <- arrow_normalize. econstructor. eauto. contradiction.
  - contradiction.
Qed.

Lemma coercion_consistency_eq : forall c k T U V W,
                                  empty |- c; T ~~ tCoerce k U V W -> value_type T -> exists U1 V1 W1, T = tCoerce k U1 V1 W1.
Proof.
  intros c k T U V W HC HV.
  pose (K := HC). apply coercion_consistency in K. inversion K.
  - rewrite <- eq_normalize in H1.
    apply coercion_well_formed in HC. destruct HC as [_ [k' [WFT WFV]]].
    apply eq_kind_inv in WFV. destruct WFV as [WFU [WFV [WFW EQ]]].
    apply tcon_injective in H1. destruct H1. subst.
    apply eq_kind_invs in WFT. destruct WFT as [t1 [t2 [t3 EQ]]]. subst.
    exists t1. exists t2. exists t3. rewrite <- eq_normalize. auto.
  - unfold not in H. assert False. apply H. rewrite <- eq_normalize.
    econstructor. eauto. contradiction.
  - contradiction.
 Qed.

    
    
                                                          
Lemma coercion_consistency_univ : forall c T k U,
                                    empty |- c; T ~~ TUniv k U -> value_type T -> exists T1, T = TUniv k T1.
intros c T k U H VT.
apply coercion_consistency in H; subst.
inversion H. subst.
- exists T1. trivial.
- unfold tcon in H2. destruct ts2. simpl in H2. inversion H2.
  destruct tcon_app with (tc := TCon tc) (t := t) (ts := ts2) as [v [w E]]. rewrite E in H2. inversion H2.
- assert False. unfold not in H0. apply H0. constructor. contradiction.
- contradiction.
Qed.

(* ###################################################################### *)
(** * Canonical Forms *)


Lemma canonical_forms_fun : forall t T1 T2,
  empty |- t \in (tArrow T1 T2) ->
  uncoerced_value t ->
  exists u, t = tabs T1 u.
Proof.
  intros t T1 T2 HT HVal.
  inversion HVal; intros; subst; try inversion HT; subst; auto.
  exists t0.  auto.
Qed.

Lemma canonical_forms_tabs : forall t k T,
  empty |- t \in TUniv k T ->
  uncoerced_value t ->
  exists t', t = ttabs k t'.
Proof.
  intros. inversion H0; subst;
  inversion H; subst.
  exists t0. reflexivity.
Qed.

Lemma canonical_forms_cabs : forall t U V T k,
  empty |- t \in tCoerce k U V T ->
  uncoerced_value t        ->
  exists t', t = tcabs U V t'.
Proof.
  intros; inversion H0; subst; inversion H; subst.
  exists t0. trivial.
Qed.

Lemma values_have_value_type : forall v T,
                                 uncoerced_value v -> (empty |- v \in T) -> value_type T.
  intros.
  inversion H.
  - subst. inversion H0. rewrite <- arrow_normalize. econstructor. eauto.
  - subst. inversion H0. econstructor.
  - subst. inversion H0. rewrite <- eq_normalize. econstructor. eauto.
Qed.
  


(*

Lemma coercion_consistency_ind : forall Gamma c U V,
  (forall n, get_cvar Gamma n = None) ->
  Gamma |- c ; U ~~ V ->
  U = V.
Proof.
  intros Gamma c; generalize dependent Gamma;
  c_cases (induction c) Case; intros; inversion H0; subst;
  try (apply IHc1 in H3; apply IHc2 in H6; subst; trivial);
  try (apply IHc in H5; inversion H5; trivial).
  Case "CVar".
    rewrite H in H3. inversion H3.
  Case "CRefl".
    trivial.
  Case "CSym".
    symmetry. eapply IHc. eassumption. trivial.
  Case "CApp".
    eapply IHc1 in H3. rewrite H3. apply IHc2 in H4. rewrite H4. trivial. trivial. trivial.
  Case "CNth".
  apply IHc in H7. inversion H7. trivial. trivial.
  apply IHc in H7. inversion H7. trivial. trivial.
(*    Case "CTCoerce".
    apply IHc1 in H4; apply IHc2 in H7; apply IHc3 in H8; subst; trivial. *)
  Case "CTAbs".
    apply f_equal. apply IHc with (ext_tvar Gamma k).
    intro. simpl. rewrite H. trivial. trivial.
  Case "CTApp".
    apply IHc in H3. inversion H3. trivial.
    trivial. 
Qed.

Lemma coercion_consistency : forall c U V,
  empty |- c ; U ~~ V ->
  U = V.
Proof.
  intros. apply coercion_consistency_ind with empty c. trivial. trivial.
Qed.

*)

(* ###################################################################### *)
(** * Progress *)

(** As before, the _progress_ theorem tells us that closed, well-typed
    terms are not stuck: either a well-typed term is a value, or it
    can take an evaluation step.  The proof is a relatively
    straightforward extension of the progress proof we saw in the
    [Types] chapter. *)

Theorem progress : forall t T, 
     empty |- t \in T ->
     value t \/ exists t', t ==> t'.

(** _Proof_: by induction on the derivation of [|- t \in T].

    - The last rule of the derivation cannot be [T_Var], since a
      variable is never well typed in an empty context.

    - The [T_True], [T_False], and [T_Abs] cases are trivial, since in
      each of these cases we know immediately that [t] is a value.

    - If the last rule of the derivation was [T_App], then [t = t1
      t2], and we know that [t1] and [t2] are also well typed in the
      empty context; in particular, there exists a type [T2] such that
      [|- t1 \in T2 -> T] and [|- t2 \in T2].  By the induction
      hypothesis, either [t1] is a value or it can take an evaluation
      step.

        - If [t1] is a value, we now consider [t2], which by the other
          induction hypothesis must also either be a value or take an
          evaluation step.

            - Suppose [t2] is a value.  Since [t1] is a value with an
              arrow type, it must be a lambda abstraction; hence [t1
              t2] can take a step by [ST_AppAbs].

            - Otherwise, [t2] can take a step, and hence so can [t1
              t2] by [ST_App2].

        - If [t1] can take a step, then so can [t1 t2] by [ST_App1].

    - If the last rule of the derivation was [T_If], then [t = if t1
      then t2 else t3], where [t1] has type [Bool].  By the IH, [t1]
      either is a value or takes a step.

        - If [t1] is a value, then since it has type [Bool] it must be
          either [true] or [false].  If it is [true], then [t] steps
          to [t2]; otherwise it steps to [t3].

        - Otherwise, [t1] takes a step, and therefore so does [t] (by
          [ST_If]).
*)

Proof with eauto.
  intros t T Ht.
  remember (@empty) as Gamma.
  has_type_cases (induction Ht) Case; subst Gamma...
  Case "T_Var".
    (* contradictory: variables cannot be typed in an 
       empty context *)
    inversion H0.

  Case "T_App". 
    (* [t] = [t1 t2].  Proceed by cases on whether [t1] is a 
       value or steps... *)
    right. destruct IHHt1...
    SCase "t1 is a value".
      destruct H...
      SSCase "t1 is an uncoerced value".
        assert (exists t0, t = tabs T11 t0).
        eapply canonical_forms_fun; eauto.
        destruct H0 as [t0 Heq]. subst.
        exists ([0:=t2]t0)...
      SSCase "t1 is coerced".
      inversion Ht1; subst.
      assert (HV : value_type T1). eapply values_have_value_type. eauto. eauto.
      destruct (coercion_consistency_arrow _ _ _ _ H3 HV) as [U [V EQ]]. subst.
      exists (tcoerce (tapp t (tcoerce t2 (CSym (CNth 2 (CNth 1 c))))) (CNth 2 c))...
    SCase "t1 steps".
      inversion H as [t1' Hstp]. exists (tapp t1' t2)...
      
  Case "T_TApp".
    right. destruct IHHt...    
    SCase "t1 is a value".
      destruct H1...
      SSCase "t1 is uncoerced".
        assert (exists t0, t = ttabs k t0).
        eapply canonical_forms_tabs; eauto.
        destruct H2; subst.
        exists ([0 := T2] x)...
      SSCase "t1 in coerced".
      inversion Ht; subst.
      assert (VT: value_type T1). apply (values_have_value_type _ _ H1 H7).
      destruct (coercion_consistency_univ _ _ _ _ H5 VT) as [T E]. subst.
      exists (tcoerce (ttapp t T2) (CTApp c T2))...
      
    SCase "t1 also steps".
      inversion H1. exists (ttapp x T2)...

  Case "T_CApp".
    right. destruct IHHt...
    SCase "t is a value".
      destruct H0...
      SSCase "t is uncoerced".
        assert (exists t0, t = tcabs U1 U2 t0).
        eapply canonical_forms_cabs...
        destruct H1; subst. exists ([0:=c] x)...
      SSCase "t is coerced".
        destruct (typing_well_formed _ _ _ Ht) as [HC _].
        destruct (eq_kind_inv _ _ _ _ _ _ HC) as [K1 [K2 [K3 K4]]].
        inversion Ht; subst.
        pose (K := values_have_value_type _ _ H0 H6).
        destruct (coercion_consistency_eq _ _ _ _ _ _ H4) as [V1 [V2 [S E]]]. auto. subst.
        
        exists (tcoerce (tcapp t (CTrans (CTrans (CNth 2 (CNth 1 (CNth 1 c0))) c)
                                        (CSym (CNth 2 (CNth 1 c0)))))
                        (CNth 2 c0))...

    SCase "t steps".
      inversion H0. exists (tcapp x c)...

  Case "T_Coerce".
    destruct IHHt...
    SCase "t is a value".
      destruct H0...
    SCase "t steps". 
      right. inversion H0. exists (tcoerce x c)...
Qed.


(* [] *)

(* ###################################################################### *)
(** * Preservation *)

(** The other half of the type soundness property is the preservation
    of types during reduction.  For this, we need to develop some
    technical machinery for reasoning about variables and
    substitution.  Working from top to bottom (the high-level property
    we are actually interested in to the lowest-level technical lemmas
    that are needed by various cases of the more interesting proofs),
    the story goes like this:

      - The _preservation theorem_ is proved by induction on a typing
        derivation, pretty much as we did in the [Types] chapter.  The
        one case that is significantly different is the one for the
        [ST_AppAbs] rule, which is defined using the substitution
        operation.  To see that this step preserves typing, we need to
        know that the substitution itself does.  So we prove a...

      - _substitution lemma_, stating that substituting a (closed)
        term [s] for a variable [x] in a term [t] preserves the type
        of [t].  The proof goes by induction on the form of [t] and
        requires looking at all the different cases in the definition
        of substitition.  This time, the tricky cases are the ones for
        variables and for function abstractions.  In both cases, we
        discover that we need to take a term [s] that has been shown
        to be well-typed in some context [Gamma] and consider the same
        term [s] in a slightly different context [Gamma'].  For this
        we prove a...

      - _context invariance_ lemma, showing that typing is preserved
        under "inessential changes" to the context [Gamma] -- in
        particular, changes that do not affect any of the free
        variables of the term.  For this, we need a careful definition
        of

      - the _free variables_ of a term -- i.e., the variables occuring
        in the term that are not in the scope of a function
        abstraction that binds them.
*)


(* ###################################################################### *)
(** ** Main Theorem *)

(** We now have the tools we need to prove preservation: if a closed
    term [t] has type [T], and takes an evaluation step to [t'], then [t']
    is also a closed term with type [T].  In other words, the small-step
    evaluation relation preserves types.
*)

Lemma preservation_app_abs : forall Gamma t12 t2 T11 U,
  Gamma |- tapp (tabs T11 t12) t2 \in U ->
  Gamma |- [0 := t2] t12 \in U.
Proof.
  intros. remember (tapp (tabs T11 t12) t2) as t.
  induction H; try discriminate.
    inversion Heqt; subst.
    inversion H; subst.
    eapply substitution_preserves_typing_term_term 
    with (ext_var Gamma T0) 0 T0 t12 t2 T12 in H7.
    simpl in H7. trivial. simpl. trivial. simpl. trivial.
Qed.


Lemma preservation_tapp_tabs : forall Gamma k t12 T2 U,
  Gamma |- ttapp (ttabs k t12) T2 \in U ->
  Gamma |- [0 := T2] t12 \in U.
Proof.
  intros. remember (ttapp (ttabs k t12) T2) as t.
  induction H; try discriminate.
    inversion Heqt; subst.
    inversion H; subst.
    eapply subst_typ_preserves_typing. trivial.
    trivial.
    eauto. trivial.
Qed.

Lemma preservation_capp_cabs : forall Gamma t12 c T1 T2 U,
  Gamma |- tcapp (tcabs T1 T2 t12) c \in U ->
  Gamma |- [0 := c] t12 \in U.
Proof.                               
  intros. remember (tcapp (tcabs T1 T2 t12) c) as t.
  induction H; try discriminate.
    inversion Heqt; subst.
    inversion H; subst.
    eapply cn_substitution_preserves_typing with (x:=0) in H6.
    simpl in H6. eassumption.
    simpl. eassumption. simpl. trivial.
Qed.

Lemma coercion_deterministic : forall Gamma c U1 U2 V1 V2,
  Gamma |- c ; U1 ~~ U2 ->
  Gamma |- c ; V1 ~~ V2 ->
  U1 = V1 /\ U2 = V2.
Proof.
  intros Gamma c; generalize dependent Gamma;
  c_cases (induction c) Case; intros; inversion H; subst; inversion H0; subst;
  try (pose proof (IHc _ _ _ _ _ H2 H3); destruct H1; subst; split; trivial);
  try (pose proof (IHc1 _ _ _ _ _ H3 H4); pose proof (IHc2 _ _ _ _ _ H6 H8);
       destruct H1; destruct H2; subst; split; trivial);
  try (pose proof (IHc _ _ _ _ _ H5 H2); destruct H1;
       inversion H1; inversion H3; split; trivial);
  try (split; trivial; assumption).
  Case "CVar".
    rewrite H3 in H5. inversion H5. split; trivial.
  Case "CApp".
    pose (J := IHc1 _ _ _ _ _ H3 H6); destruct J.
    pose (K := IHc2 _ _ _ _ _ H4 H7); destruct K.
    subst. split; trivial.
  Case "CNth".
  pose (J := IHc _ _ _ _ _ H7 H6); destruct J.
  inversion H1. inversion H8. split; trivial.
  pose (J := IHc _ _ _ _ _ H7 H6); destruct J.
  inversion H1. inversion H8. split; trivial.
  Case "CTAbs".
   pose (J := IHc _ _ _ _ _ H3 H5); destruct J.
   subst. split; trivial.  
  Case "CTApp".
    pose proof (IHc _ _ _ _ _ H3 H4). destruct H1. inversion H1.
    inversion H2. subst. split; trivial.
Qed.

Theorem types_deterministic : forall Gamma t S T,
  Gamma |- t \in S ->
  Gamma |- t \in T ->
  S = T.
Proof.
  intros Gamma t; generalize dependent Gamma; t_cases (induction t) Case;
  intros; inversion H; subst; inversion H0; subst;
  try (pose proof (IHt _ _ _ H5 H6); subst; trivial);
  try (pose proof (IHt _ _ _ H3 H4); inversion H1; trivial);
  try (pose proof (IHt1 _ _ _ H4 H5); inversion H1; trivial);
  try (pose proof (IHt _ _ _ H4 H5); inversion H1; trivial).
  Case "tvar".
  rewrite H4 in H6. inversion H6. trivial.
  Case "tabs".
  f_equal. eapply IHt;  eauto.
  Case "tcabs". 
  f_equal. eapply kinds_unique. eauto.  eauto. 
  Case "tcoerce".
    pose proof (coercion_deterministic _ _ _ _ _ _ H4 H5). destruct H1; trivial.
Qed.




Lemma wf_type_weakening : forall Gamma T k,
  well_formed_context Gamma ->
  well_formed_type empty T k ->
  well_formed_type Gamma T k.
Proof.
  intros Gamma. induction Gamma; intros.
  Case "empty".
    trivial.
  Case "ext_var".
    apply wf_weakening_var. apply IHGamma. inversion H. trivial. trivial.
  Case "ext_tvar".
    assert (tshift 0 T =  T). eapply no_tvars_tshift_ind. eassumption. trivial.
    rewrite <- H1. apply type_weakening_tvar. inversion H. apply IHGamma.
    trivial. trivial.
  Case "ext_cvar".
    destruct p. apply type_weakening_cvar. apply IHGamma. inversion H.
    trivial. trivial.
Qed.

Lemma coercion_weakening : forall Gamma c T U,
                             well_formed_context Gamma ->
                             empty |- c ; T ~~ U       ->
                                          Gamma |- c ; T ~~ U.
Proof.
  intros Gamma; induction Gamma; intros; trivial.
  - apply coercion_weakening_var with 0. auto. simpl. apply IHGamma.
    inversion H. auto. auto.
  - inversion H.
    assert (E1 : cshift_typ 0 c = c). eapply no_cvars_cshift_typ_ind; eauto.
    destruct (coercion_well_formed _ _ _ _ H0) as [k1 [K1 [K2 K3]]].
    assert (E2 : tshift 0 T = T). eapply no_tvars_tshift_ind; eauto.
    assert (E3 : tshift 0 U = U). eapply no_tvars_tshift_ind; eauto.
    rewrite <- E1. rewrite <- E2. rewrite <- E3.
    apply coercion_weakening_tvar.     apply IHGamma. auto. auto.
  - destruct p.
    assert (E1 : cshift 0 c = c). eapply no_cvars_cshift_ind; eauto.
    rewrite <- E1. inversion H.
    apply coercion_weakening with k. auto.
    apply IHGamma. auto. auto. auto. auto.
Qed.    

Lemma typing_weakening : forall Gamma t T,
  well_formed_context Gamma ->
  empty |- t \in T          ->
  Gamma |- t \in T.
Proof.
  intros Gamma; induction Gamma; intros.
  Case "empty".
    trivial.
  Case "ext_var".
    assert (shift 0 t0 = t0). eapply no_vars_shift. eassumption. rewrite <- H1. 
    inversion H. apply typing_weakening_var. trivial. trivial.
    apply IHGamma. trivial. trivial.
  Case "ext_tvar".
    assert (shift_typ 0 t = t). eapply no_tvars_shift_typ_ind. eassumption.
    trivial. rewrite <- H1. inversion H. remember H0 as Ht. clear HeqHt.
    apply typing_well_formed in H0.
    destruct H0. assert (tshift 0 T = T). eapply no_tvars_tshift_ind.
    eassumption. trivial. rewrite <- H6.
    apply typing_weakening_tvar_ind with Gamma k. econstructor.
    apply IHGamma. trivial. trivial.
  Case "ext_cvar".  
    destruct p. assert (shift_cn 0 t = t). eapply no_cvars_shift_cn_ind.
    eassumption. trivial. rewrite <- H1.
    apply typing_weakening_cvar_ind. trivial.
    simpl. apply IHGamma. inversion H. trivial. trivial.
Qed.





  

Theorem preservation : forall Gamma t t' T,
     Gamma |- t \in T  ->
     t ==> t'  ->
     Gamma |- t' \in T.

(** _Proof_: by induction on the derivation of [|- t \in T].

    - We can immediately rule out [T_Var], [T_Abs], [T_True], and
      [T_False] as the final rules in the derivation, since in each of
      these cases [t] cannot take a step.

    - If the last rule in the derivation was [T_App], then [t = t1
      t2].  There are three cases to consider, one for each rule that
      could have been used to show that [t1 t2] takes a step to [t'].

        - If [t1 t2] takes a step by [ST_App1], with [t1] stepping to
          [t1'], then by the IH [t1'] has the same type as [t1], and
          hence [t1' t2] has the same type as [t1 t2].

        - The [ST_App2] case is similar.

        - If [t1 t2] takes a step by [ST_AppAbs], then [t1 =
          \x:T11.t12] and [t1 t2] steps to [[x:=t2]t12]; the
          desired result now follows from the fact that substitution
          preserves types.

    - If the last rule in the derivation was [T_If], then [t = if t1
      then t2 else t3], and there are again three cases depending on
      how [t] steps.

        - If [t] steps to [t2] or [t3], the result is immediate, since
          [t2] and [t3] have the same type as [t].

        - Otherwise, [t] steps by [ST_If], and the desired conclusion
          follows directly from the induction hypothesis.
*)

Proof with eauto.
  intros Gamma t t' T HT. generalize dependent t'.   
  has_type_cases (induction HT) Case;
       intros t' HE; 
       try solve [inversion HE; subst; auto].
  Case "T_App".
    inversion HE; subst...
    (* Most of the cases are immediate by induction, 
       and [eauto] takes care of them *)
    SCase "ST_AppAbs".
      eapply preservation_app_abs.
      inversion HT1... 
    SCase "ST_PushApp".
      inversion HT1; subst. remember H4 as Hy. clear HeqHy. 
      apply (typing_weakening Gamma) in H3.
      pose proof (types_deterministic _ _ _ _ H3 H6). subst.
      destruct (coercion_well_formed _ _ _ _ Hy) as [HG [k [HU HV]]].
      econstructor. eapply C_ARight with (U2 := U2). eapply arrow_kind_inv2. eauto.
      eapply arrow_kind_inv2. eauto. eassumption.
      econstructor. eassumption. econstructor. econstructor. 
      eapply C_ARight with (U1 := (TCon TArrow)) (V1 := (TCon TArrow)).
         eapply arrow_kind_inv1; eauto.
         eapply arrow_kind_inv1; eauto.
      eapply C_ALeft with (U2 := U2). econstructor. econstructor. apply arrKind.
      eapply arrow_kind_inv1; eauto. econstructor. econstructor. apply arrKind.
      eapply arrow_kind_inv1. eauto. eassumption.
      eassumption. apply term_context with v1 T1. assumption.
  Case "T_TApp".
    inversion HE; subst...
    SCase "ST_TAppTAbs".
      inversion HT; subst. apply preservation_tapp_tabs with k. econstructor. eassumption.
      trivial. trivial. 
    SCase "ST_PushTApp".
      inversion HT; subst. remember H4 as Hy; clear HeqHy.
      apply (typing_weakening Gamma) in H4.
      pose proof (types_deterministic _ _ _ _ H4 H9). subst.
      apply (wf_type_weakening Gamma) in H6.
      pose proof (kinds_unique _ _  _ H _ H6). subst.
      econstructor. econstructor. eassumption. trivial. econstructor.
      eassumption. trivial. trivial. trivial. trivial.
  Case "T_CApp".
    inversion HE; subst...
    SCase "ST_CAppCAbs".
      eapply preservation_capp_cabs...
    SCase "ST_PushCApp".
      eapply (coercion_weakening Gamma) in H6.  
      destruct (props_unique _ _ _ _ H _ _ H6). subst.
      inversion HT; subst. remember H4 as Hy; clear HeqHy.
      apply (typing_weakening Gamma) in H3.
      pose proof (types_deterministic _ _ _ _ H3 H9). subst.
      pose (K := coercion_well_formed _ _ _ _ H7).
        destruct K as [WFG [k1 [WF1 WF2]]].
      destruct (eq_kind_inv _ _ _ _ _ _ WF1) as
            [K1 [K2 [K3 K4]]].
      destruct (eq_kind_inv _ _ _ _ _ _ WF2) as
          [J1 [J2 [J3 J4]]]. subst.
      apply (wf_type_weakening Gamma) in H4.
      assert (k = k0). eapply kinds_unique with Gamma U0. auto. auto. subst.
      eapply T_Coerce with (T1 := U).
      apply C_ARight with (U1 := TApp (TApp (TCon (TEq k0)) U3) U4)
                            (k := KStar)
                          (V1 := TApp (TApp (TCon (TEq k0)) U0) U5); eauto.
      econstructor; eauto.
      apply C_Trans with (V := U5).
      apply C_Trans with (V := U0).
      eapply C_ARight with (U1 := (TCon (TEq k0))) (V1:= TCon (TEq k0)); eauto.
      eapply C_ALeft  with (U2 := U4) (V2:= U5); eauto.
        econstructor. econstructor. eapply coerceKind. eauto.
        econstructor. econstructor. eapply coerceKind. eauto.
        eapply C_ALeft with (U2 := U) (V2 := T).
        econstructor. econstructor. econstructor. eapply coerceKind. eauto.
        eauto. econstructor. econstructor. econstructor. eapply coerceKind.
        eauto. eauto. assumption.
      eauto. (* U0 ~~ U5 *)
      econstructor.
      eapply C_ARight with (U1 := TApp (TCon (TEq k0)) U3)
                             (V1 := TApp (TCon (TEq k0)) U0).
      eassumption. trivial.
      eapply C_ALeft with (U2 := U) (V2 := T).
      econstructor. econstructor. econstructor. eapply coerceKind. eauto.
      eauto. econstructor. econstructor. econstructor. eapply coerceKind.
      eauto. eauto. trivial. trivial.
      eapply term_context. eauto.
      eapply term_context. eauto.
  Case "T_Coerce".
    inversion HE; subst...
    SCase "ST_CTrans".
      inversion HT. econstructor. econstructor. eassumption. trivial.
      trivial.
Qed.

(* ###################################################################### *)
(** * Type Soundness *)

(** Put progress and preservation together and show that a well-typed
    term can _never_ reach a stuck state.  *)

Definition normal_form {X:Type} (R:relation X) (t:X) : Prop :=
  ~ exists t', R t t'.

Definition stuck (t:tm) : Prop :=
  (normal_form step) t /\ ~ value t.

Corollary soundness : forall t t' T,
  empty |- t \in T -> 
  t ==>* t' ->
  ~(stuck t').
Proof.
  intros t t' T Hhas_type Hmulti. unfold stuck.
  intros [Hnf Hnot_val]. unfold normal_form in Hnf.
  induction Hmulti.
  assert (value x \/ exists t', x ==> t')
    by (eapply progress; apply Hhas_type); inversion H.
  Case "Hmulti 1".
    apply Hnot_val. assumption.
    apply Hnf; assumption.
  Case "Hmulti 2".
    apply IHHmulti. eapply preservation. apply Hhas_type.
    assumption. assumption. assumption.
Qed.

End SYSTEMFCPROP.