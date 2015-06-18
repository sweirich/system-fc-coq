Require Import SystemFC.
Require Export Shifting.
Require Export Substitution.

Module TYPING.
Import SYSTEMFC.
Import SHIFTING.
Import SUBSTITUTION.

(* ###################################################################### *)
(** ** Typing *)

(* ################################### *)
(** *** Contexts *)

Parameter Sigma : tycon -> option kind.

Axiom arrKind : Sigma TArrow = Some (KArrow KStar (KArrow KStar KStar)).
Axiom coerceKind : forall k,
   Sigma (TEq k) = Some (KArrow k (KArrow k (KArrow KStar KStar))).

Inductive context : Set :=
  | empty    : context
  | ext_var  : context -> ty -> context
  | ext_tvar : context -> kind -> context
  | ext_cvar : context -> ty * ty -> context.

Definition opt_map {A B : Type} (f : A -> B) (x : option A) :=
  match x with
  | Some x => Some (f x)
  | None => None
  end.

Definition opt_map_prod {A B : Type} (f : A -> B) (p : option (A * A)) :=
  match p with
    | Some (x, y) => Some (f x, f y)
    | None        => None
  end.

Fixpoint get_var (E : context) (x : nat) : option ty :=
  match E with
    | empty => None
    | ext_var E' T =>
      match x with
        | O   => Some T
        | S y => get_var E' y
      end
    | ext_tvar E' k => opt_map (tshift 0) (get_var E' x)
    | ext_cvar E' _ => get_var E' x
  end.

Fixpoint get_tvar (E : context) (N : nat) : option kind :=
  match E with
    | empty =>  None
    | ext_var E' _ => get_tvar E' N
    | ext_tvar E' k  =>
      match N with
        | O => Some k
        | S N' => get_tvar E' N'
      end
    | ext_cvar E' _ => get_tvar E' N
  end.

Fixpoint get_cvar (E : context) (N : nat) : option (ty * ty) :=
  match E with
    | empty => None
    | ext_var E' _  => get_cvar E' N
    | ext_tvar E' _  => opt_map_prod (tshift 0) (get_cvar E' N)
    | ext_cvar E' c =>
      match N with
        | O    => Some c
        | S N' => get_cvar E' N'
      end
  end.


(* ################################### *)
(** *** Well Formed Types *)

Fixpoint wf_ty (Gamma : context) (T : ty) (k : kind) : Prop :=
  match T with
    | TVar X        => get_tvar Gamma X = Some k
    | TCon tc       => Sigma tc = Some k
    | TApp T1 T2    => exists k', wf_ty Gamma T1 (KArrow k' k) /\ wf_ty Gamma T2 k'
    | TUniv k' T    => k = KStar /\ wf_ty (ext_tvar Gamma k') T KStar

  end.

Inductive well_formed_type (Gamma : context) : ty -> kind -> Prop :=
  | WF_TVar : forall X k,
      get_tvar Gamma X = Some k ->
      well_formed_type Gamma (TVar X) k
  | WF_TCon : forall X k,
      Sigma X = Some k ->
      well_formed_type Gamma (TCon X) k
  | WF_TApp : forall T1 T2 k' k,
      well_formed_type Gamma T1 (KArrow k' k) ->
      well_formed_type Gamma T2 k' ->
      well_formed_type Gamma (TApp T1 T2) k
  | WF_TUniv : forall k T,
      well_formed_type (ext_tvar Gamma k) T KStar ->
      well_formed_type Gamma (TUniv k T) KStar.

Lemma wf_type_correct : forall Gamma T k,
  well_formed_type Gamma T k <-> wf_ty Gamma T k.
Proof.

  split; intros.
  Case "->".
    induction H; try split; try split; trivial.
    exists k'. split; trivial.
  Case "<-".
    generalize dependent Gamma. generalize dependent k. induction T; intros k' Gamma H.
    constructor. simpl in H. trivial.
    constructor. simpl in H. trivial.
    inversion H. destruct H0.
    apply WF_TApp with (k' := x). apply IHT1. trivial.
      apply IHT2. trivial.
    inversion H. subst.
      constructor. simpl in H. apply IHT. trivial.
Qed.



(* ################################### *)
(** *** Well Formed Contexts *)

Inductive well_formed_context : context -> Prop :=
  | WFC_empty :
      well_formed_context empty
  | WFC_ext_var : forall T Gamma,
      well_formed_type Gamma T KStar ->
      well_formed_context Gamma ->
      well_formed_context (ext_var Gamma T) 
  | WFC_ext_tvar : forall Gamma k,
      well_formed_context Gamma ->
      well_formed_context (ext_tvar Gamma k)
  | WFC_ext_cvar : forall Gamma U V k,
      well_formed_context Gamma ->
      well_formed_type Gamma U k ->
      well_formed_type Gamma V k ->
      well_formed_context (ext_cvar Gamma (U, V)).



(* ################################### *)
(** *** Coercion Relation *)


Reserved Notation "Gamma '|-' t ';' T1 '~~' T2" (at level 40).
    
Inductive well_formed_coercion (Gamma : context) : cn -> ty -> ty -> Prop :=
  | C_Var : forall x T1 T2,
      well_formed_context Gamma        ->
      get_cvar Gamma x = Some (T1, T2) ->
      Gamma |- CVar x ; T1 ~~ T2
  | C_Refl : forall T k,
      well_formed_context Gamma ->
      well_formed_type Gamma T k ->
      Gamma |- CRefl T ; T ~~ T
  | C_Sym : forall c T1 T2,
      Gamma |- c ; T1 ~~ T2 ->
      Gamma |- CSym c ; T2 ~~ T1
  | C_Trans : forall c1 c2 U V W,
      Gamma |- c1 ; U ~~ V ->
      Gamma |- c2 ; V ~~ W ->
      Gamma |- CTrans c1 c2 ; U ~~ W
  | C_App : forall c1 c2 U1 U2 V1 V2,
      Gamma |- c1 ; U1 ~~ V1 ->
      Gamma |- c2 ; U2 ~~ V2 ->
      well_formed_type Gamma (TApp U1 U2) KStar ->
      well_formed_type Gamma (TApp V1 V2) KStar ->                    
      Gamma |- CApp c1 c2 ; TApp U1 U2 ~~ TApp V1 V2
  | C_Forall : forall c U V k,
      ext_tvar Gamma k |- c ; U ~~ V ->
      well_formed_type Gamma (TUniv k U) KStar ->
      well_formed_type Gamma (TUniv k V) KStar ->
      Gamma |- CTAbs k c ; TUniv k U ~~ TUniv k V

  | C_ALeft : forall c U1 U2 V1 V2 k1 k2,
      well_formed_type Gamma U1 (KArrow k1 k2) ->
      well_formed_type Gamma V1 (KArrow k1 k2) ->
      Gamma |- c ; (TApp U1 U2) ~~ (TApp V1 V2) ->
      Gamma |- CNth 1 c ; U1 ~~ V1
                                          
  | C_ARight : forall c U1 U2 V1 V2 k,
      well_formed_type Gamma U2 k ->
      well_formed_type Gamma V2 k ->
      Gamma |- c ; (TApp U1 U2) ~~ (TApp V1 V2) ->
      Gamma |- CNth 2 c ; U2 ~~ V2

  | C_Inst : forall c U V T k,
      Gamma |- c ; TUniv k U ~~ TUniv k V ->
      well_formed_type Gamma T k      ->
      Gamma |- CTApp c T ; ([0 := T] U) ~~ ([0 := T] V)
    
where "Gamma '|-' c ';' T1 '~~' T2" := (well_formed_coercion Gamma c T1 T2).

Tactic Notation "coercion_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "C_Var"   | Case_aux c "C_Refl" 
  | Case_aux c "C_Sym"   | Case_aux c "C_Trans" 
  | Case_aux c "C_App"   | Case_aux c "C_Forall"
  | Case_aux c "C_ALeft" | Case_aux c "C_ARight"
  | Case_aux c "C_Inst" ].

Hint Constructors well_formed_coercion.



(* ################################### *)
(** *** Typing Relation *)

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).


Definition tArrow (t1 : ty) (t2:ty) := TApp (TApp (TCon TArrow) t1) t2.
Definition tCoerce k t1 t2 t3 := TApp (TApp (TApp (TCon (TEq k)) t1) t2) t3.
Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      well_formed_context Gamma ->
      get_var Gamma x = Some T ->
      Gamma |- tvar x \in T
  | T_Abs : forall Gamma T11 T12 t12,
      well_formed_type Gamma T11 KStar ->               
      ext_var Gamma T11 |- t12 \in T12 -> 
      Gamma |- tabs T11 t12 \in tArrow T11 T12
  | T_App : forall T11 T12 Gamma t1 t2,
      Gamma |- t1 \in tArrow T11 T12 -> 
      Gamma |- t2 \in T11 -> 
      Gamma |- tapp t1 t2 \in T12
  | T_TAbs : forall Gamma t T k,
      ext_tvar Gamma k |- t \in T ->
      Gamma |- ttabs k t \in (TUniv k T)
  | T_TApp : forall Gamma t1 T12 T2 k,
      Gamma |- t1 \in (TUniv k T12) ->
      well_formed_type Gamma T2 k  ->
      well_formed_context Gamma   ->
      Gamma |- ttapp t1 T2 \in [0 := T2] T12
  | T_CAbs : forall Gamma t T1 T2 T k,
      ext_cvar Gamma (T1, T2) |- t \in T ->
      well_formed_type Gamma T1 k ->
      well_formed_type Gamma T2 k ->
      Gamma |- tcabs T1 T2 t \in tCoerce k T1 T2 T
  | T_CApp : forall Gamma U1 U2 T t c k,
      Gamma |- t \in (tCoerce k U1 U2 T) ->
      Gamma |- c ; U1 ~~ U2             ->
      Gamma |- tcapp t c \in T
  | T_Coerce : forall Gamma t c T1 T2,
      Gamma |- c ; T1 ~~ T2 ->
      Gamma |- t \in T1    ->
      Gamma |- tcoerce t c \in T2

      
where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var"  | Case_aux c "T_Abs" 
  | Case_aux c "T_App"  | Case_aux c "T_TAbs" 
  | Case_aux c "T_TApp" | Case_aux c "T_CAbs"
  | Case_aux c "T_CApp" | Case_aux c "T_Coerce" ].

Hint Constructors has_type.


(* ####################################################### *)
(** *** Uniqueness: our judgements are syntax directed.    *)

Lemma kinds_unique :
  forall Gamma U k1, well_formed_type Gamma U k1 ->
    forall k2, well_formed_type Gamma U k2 -> k1 = k2.
Proof.
  induction 1; intros k2 H2; inversion H2.
  rewrite H in H1. inversion H1. auto.
  rewrite H in H1. inversion H1. auto.
  apply IHwell_formed_type1 in H4.
  apply IHwell_formed_type2 in H6. subst.
  inversion H4. auto.
  auto.
Qed.


Lemma props_unique :
  forall Gamma cn U1 V1,
    Gamma |- cn ; U1 ~~ V1 ->
      forall U2 V2, Gamma |- cn ; U2 ~~ V2 ->
                                  U1 = U2 /\ V1 = V2.
Proof.
  induction 1; intros U1' U2' K2; inversion K2; subst.
  - rewrite H0 in H3. inversion H3. auto.
  - auto.
  - destruct (IHwell_formed_coercion _ _ H1). subst. auto.
  - destruct (IHwell_formed_coercion1 _ _ H3).
    destruct (IHwell_formed_coercion2 _ _ H6). subst. auto.
  - destruct (IHwell_formed_coercion1 _ _ H5).
    destruct (IHwell_formed_coercion2 _ _ H6). subst. auto.
  - destruct (IHwell_formed_coercion _ _ H4). subst. auto.
  - destruct (IHwell_formed_coercion _ _ H5).
    inversion H2. inversion H6. subst. auto.
  - destruct (IHwell_formed_coercion _ _ H5).
    inversion H2. inversion H6. subst. auto.
  - destruct (IHwell_formed_coercion _ _ H3).
    inversion H1. inversion H2. subst. auto.
Qed.

Lemma types_unique:
  forall Gamma tm T1, (Gamma |- tm \in T1) ->
                      forall T2,( Gamma |- tm \in T2) -> T1 = T2.
Proof.
  induction 1; intros T' H2; inversion H2; subst.
  - rewrite H0 in H5. inversion H5. trivial.
  - rewrite IHhas_type with T1; trivial.
  - pose (J:= IHhas_type1 _ H5). inversion J. trivial.
  - rewrite IHhas_type with T0; trivial.
  - pose (J:= IHhas_type _ H5). inversion J. trivial.
  - rewrite IHhas_type with T4; trivial.
    rewrite kinds_unique with Gamma T1 k k0; trivial.
  - pose (J:= IHhas_type _ H5). inversion J. trivial.
  - destruct (props_unique _ _ _ _ H _ _ H5). trivial.
Qed.    


(* ####################################################### *)
(** *** Type constructor multi application                 *)

Fixpoint tcon_aux t ts :=
  match ts with
    | nil => t
    | hd :: tl => tcon_aux (TApp t hd) tl
  end.
Definition tcon tc ts := tcon_aux (TCon tc) ts.

Lemma arrow_normalize : forall t1 t2,
                          tcon TArrow (t1 :: t2 :: nil) =
                          tArrow t1 t2.
Proof.
  intros. unfold tcon. simpl. trivial.
Qed.

Lemma eq_normalize : forall k t1 t2 t3,
                       tcon (TEq k) (t1 :: t2 :: t3 :: nil) =
                       tCoerce k t1 t2 t3.
Proof.
  intros. unfold tcon. simpl. trivial.
Qed.





End TYPING.