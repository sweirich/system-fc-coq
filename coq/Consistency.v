Require Import SFC.Weakening.
Require Export SFC.SubstProp.
Require Export SFC.Evaluation.
Require Import SFC.SystemFC.
Require Import SFC.Shifting.
Require Import SFC.Substitution.
Require Import SFC.Typing.
Require Import SFC.Utils.
Require Import Coq.Program.Equality.


(* ############################################################### *)

Inductive value_type : ty -> Prop :=
| v_univ : forall k T,
             value_type (TUniv k T)
| v_con  : forall tc ts t,
             t = tcon tc ts -> value_type t.

Hint Constructors value_type.


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
Lemma coercion_consistency : forall c U V,
   empty |- c ; U ~~ V ->
   consistent_equality U V.
Proof.
  safe_admit.
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
Proof.
  safe_admit.
Qed.
 *)

Lemma kinds_oc : forall k k0, ~(k = KArrow k0 k).
  unfold not.
  intros. induction k. inversion H.
  inversion H. apply IHk2. auto.
Qed.

Lemma arg_kinds_oc : forall ks k1 k, k = KArrow k1 (arg_kinds ks k) -> False.
  induction k. intros. inversion H.
  intro H1. inversion H1.
Proof.
  safe_admit.
Qed.
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

Lemma tcon_injective :
  forall ts1 ts2 tc1 tc2,
    tcon tc1 ts1 = tcon tc2 ts2 -> tc1 = tc2 /\ ts1 = ts2.
Proof.
  safe_admit.
Qed.
