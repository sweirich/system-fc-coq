Require Export SFC.Shifting.
Require Import Omega.

(* ###################################################################### *)
(** *** Substitution *)


Class Subst (X S T : Type) := {
  do_subst : X -> S -> T -> T
}.
Notation "'[' x ':=' s ']' t" := (do_subst x s t) (at level 20).


Fixpoint subst_coer_fix (x:nat) (d:cn) (c:cn) : cn :=
  match c with
    | CAxiom ks t u => CAxiom ks t u
    | CVar y => 
      if eq_nat_dec x y then d
      else if le_lt_dec x y then CVar (y-1)
           else CVar y
    | CRefl T      => CRefl T
    | CSym c       => CSym (subst_coer_fix x d c)
    | CTrans c1 c2 => CTrans (subst_coer_fix x d c1) (subst_coer_fix x d c2)
    | CApp c1 c2   => CApp (subst_coer_fix x d c1) (subst_coer_fix x d c2)
    | CNth n c     => CNth n (subst_coer_fix x d c)
    | CTAbs k c    => CTAbs k (subst_coer_fix x (cshift_typ 0 d) c)
    | CTApp c T    => CTApp (subst_coer_fix x d c) T
  end.

Instance subst_cn : Subst nat cn cn := {
  do_subst := subst_coer_fix
}.


Inductive subst_coercion : cn -> nat -> cn -> cn -> Prop :=
                                                     
  | sc_var_here : forall d x,
      subst_coercion d x (CVar x) d
                                   
  | sc_var_lt : forall d x x',
      x < x' ->
      subst_coercion d x (CVar x') (CVar (x' - 1))
  | sc_var_gt : forall d x x',
      x > x' ->
      subst_coercion d x (CVar x') (CVar x')
  | sc_axiom : forall d x ks t u,
      subst_coercion d x (CAxiom ks t u) (CAxiom ks t u)
  | sc_refl : forall d x T,
      subst_coercion d x (CRefl T) (CRefl T)
  | sc_sym : forall d x c c',
      subst_coercion d x c c' ->
      subst_coercion d x (CSym c) (CSym c')
  | sc_trans : forall d x c1 c1' c2 c2',
      subst_coercion d x c1 c1' ->
      subst_coercion d x c2 c2' ->
      subst_coercion d x (CTrans c1 c2) (CTrans c1' c2')
  | sc_cpp : forall d x c1 c1' c2 c2',
      subst_coercion d x c1 c1' ->
      subst_coercion d x c2 c2' ->
      subst_coercion d x (CApp c1 c2) (CApp c1' c2')
  | sc_nth : forall d x n c c',
      subst_coercion d x c c' ->
      subst_coercion d x (CNth n c) (CNth n c')
  | sc_tabs : forall d x c c' k,
      subst_coercion (cshift_typ 0 d) x c c' ->
      subst_coercion d x (CTAbs k c) (CTAbs k c')
  | sc_tapp : forall d x c c' T,
      subst_coercion d x c c' ->
      subst_coercion d x (CTApp c T) (CTApp c' T).

Hint Constructors subst_coercion.


 
Lemma subst_coercion_correct : forall d x c c',
  [x:=d]c = c' <-> subst_coercion d x c c'.
Proof.
  intros d x c. split.
  Case "->".
    generalize dependent c'. generalize dependent x.
    generalize dependent d.
    induction c; intros d x c' H; simpl in H;
      try (subst; constructor; apply IHc; trivial).
    SCase "c = CVar n".
      destruct (eq_nat_dec x n) in H; subst.
      SSCase "x = n".
        constructor.
      SSCase "x <> n".
        destruct (le_lt_dec x n).
          constructor. omega. 
          constructor. omega.
    SCase "c = CTrans c1 c2".
      rewrite <- H. constructor.
      apply IHc1. trivial.
      apply IHc2. trivial.
    SCase "c = CApp c1 c2".
      rewrite <- H. constructor.
      apply IHc1. trivial.
      apply IHc2. trivial.
      (*
    SCase "c = CTCoerce c1 c2 c3".
      rewrite <- H. constructor.
      apply IHc1. trivial.
      apply IHc2. trivial.
      apply IHc3. trivial. *)
  Case "<-".
    intro H. induction H; simpl;
    subst; try reflexivity; try assumption.
    destruct (eq_nat_dec x x). trivial. omega.
    destruct (eq_nat_dec x x'). omega. destruct le_lt_dec.
    trivial. omega. 
    destruct (eq_nat_dec x x'). omega. destruct le_lt_dec.
    omega. trivial.
Qed.  

(* Term Sustitution *)
Fixpoint subst_term_fix (x:nat) (s:tm) (t:tm) : tm :=
  match t with
  | tvar y => 
    if eq_nat_dec x y then s
    else if le_lt_dec x y then tvar (y-1)
         else tvar y
  | tabs T t1 => 
      tabs T (subst_term_fix (S x) (shift 0 s) t1) 
  | tapp t1 t2 => 
      tapp (subst_term_fix x s t1) (subst_term_fix x s t2)
  | ttabs k t =>
      ttabs k (subst_term_fix x (shift_typ 0 s) t)
  | ttapp t T =>
      ttapp (subst_term_fix x s t) T
  | tcabs T1 T2 t =>
      tcabs T1 T2 (subst_term_fix x (shift_cn 0 s) t)
  | tcapp t c =>
      tcapp (subst_term_fix x s t) c
  | tcoerce t c =>
      tcoerce (subst_term_fix x s t) c
  end.

Instance subst_tm_tm : Subst nat tm tm := {
  do_subst := subst_term_fix
}.


Inductive subst_term : tm -> nat -> tm -> tm -> Prop := 
  | s_var1 : forall s x,
      subst_term s x (tvar x) s
  | s_var2 : forall s x x',
      x < x' ->
      subst_term s x (tvar x') (tvar (x' - 1))
  | s_var3 : forall s x x',
      x > x' ->
      subst_term s x (tvar x') (tvar x')
  | s_tabs : forall s x T t t',
      subst_term (shift 0 s) (S x) t t' ->
      subst_term s x (tabs T t) (tabs T t')
  | s_tapp : forall s x t1 t2 t1' t2',
      subst_term s x t1 t1' ->
      subst_term s x t2 t2' ->
      subst_term s x (tapp t1 t2) (tapp t1' t2')
  | s_ttabs : forall s x t t' k,
      subst_term (shift_typ 0 s) x t t' ->
      subst_term s x (ttabs k t) (ttabs k t')
  | s_ttapp : forall s x t t' T,
      subst_term s x t t' ->
      subst_term s x (ttapp t T) (ttapp t' T)
  | s_tcabs : forall s x t t' T1 T2,
      subst_term (shift_cn 0 s) x t t' ->
      subst_term s x (tcabs T1 T2 t) (tcabs T1 T2 t')
  | s_tcapp : forall s x t t' c,
      subst_term s x t t' ->
      subst_term s x (tcapp t c) (tcapp t' c)
  | s_tcoerce : forall s x t t' c,
      subst_term s x t t' ->
      subst_term s x (tcoerce t c) (tcoerce t' c).


Hint Constructors subst_term.

Theorem subst_term_correct : forall s x t t',
  [x:=s]t = t' <-> subst_term s x t t'.
Proof.
  intros s x t. split.
  Case "->".
    generalize dependent t'. generalize dependent x.
    generalize dependent s.
    induction t; intros s x t' H; simpl in H;
      try (subst; constructor; apply IHt; trivial).
    SCase "t = tvar i".
      destruct (eq_nat_dec x n) in H; subst.
      SSCase "x = n".
        constructor.
      SSCase "x <> n".
        destruct (le_lt_dec x n).
          constructor. omega. 
          constructor. omega.
    SCase "t = tapp t1 t2".
      rewrite <- H. constructor.
      apply IHt1. reflexivity.
      apply IHt2. reflexivity.
  Case "<-".
    intro H. induction H; simpl;
    subst; try reflexivity; try assumption.
    destruct (eq_nat_dec x x). trivial. omega.
    destruct (eq_nat_dec x x'). omega. destruct le_lt_dec.
    trivial. omega. 
    destruct (eq_nat_dec x x'). omega. destruct le_lt_dec.
    omega. trivial.
Qed.

(** [] *)


(* Type in Type Sustitution *)

Fixpoint subst_type_in_type_fix (I:nat) (P:ty) (T:ty) : ty :=
  match T with
  | TVar N =>
      if eq_nat_dec I N then P
      else if le_lt_dec I N then TVar (N-1)
        else TVar N
  | TCon N => TCon N
  | TApp T1 T2 =>
      TApp (subst_type_in_type_fix I P T1) (subst_type_in_type_fix I P T2)
  | TUniv k T   => TUniv k (subst_type_in_type_fix (I + 1) (tshift 0 P) T)
  end.

Instance subst_ty_ty : Subst nat ty ty := {
  do_subst := subst_type_in_type_fix
}.


Inductive subst_type_in_type (T:ty) (I:nat) : ty -> ty -> Prop :=
  | s_var_eq :
    subst_type_in_type T I (TVar I) T
  | s_var_lt : forall N,
      N < I ->
      subst_type_in_type T I (TVar N) (TVar N)
  | s_var_gt : forall N,
      N > I ->
      subst_type_in_type T I (TVar N) (TVar (N-1))
  | s_con : forall N,
      subst_type_in_type T I (TCon N) (TCon N)
  | s_app : forall T1 T2 T1' T2',
      subst_type_in_type T I T1 T1' ->
      subst_type_in_type T I T2 T2' ->
      subst_type_in_type T I (TApp T1 T2) (TApp T1' T2')
  | s_univ : forall T1 T2 k,
      subst_type_in_type (tshift 0 T) (I+1) T1 T2 ->
      subst_type_in_type T I (TUniv k T1) (TUniv k T2).


Lemma subst_type_in_type_correct : forall N P T1 T2,
  [N:=P]T1 = T2 <-> subst_type_in_type P N T1 T2.
Proof.

  intros. split.
  Case "->".
    generalize dependent N; generalize dependent P;
    generalize dependent T2;
    induction T1; intros; simpl in H.
    SCase "T1 = TVar n".
      destruct (eq_nat_dec N n); subst.
      SSCase "N = n".
        constructor.
      SSCase "N <> n".
        destruct (le_lt_dec N n); subst.
        SSSCase "N <= n".
          apply s_var_gt. unfold gt.
          apply le_lt_or_eq in l. inversion l; subst.
          assumption. apply ex_falso_quodlibet; apply n0; reflexivity.
        SSSCase "N > n".
        apply s_var_lt. assumption.
    SCase "T1 = TCon X".
        subst. constructor.
    SCase "T1 = TApp T11 T12".
      rewrite <- H. constructor.
      apply IHT1_1. reflexivity.
      apply IHT1_2. reflexivity.
    SCase "T2 = TUniv T".
      rewrite <- H. constructor. apply IHT1. reflexivity.
(*    SCase "T2 = TCoerce T".
      rewrite <- H. constructor. apply IHT1_1. trivial.
      apply IHT1_2; trivial. apply IHT1_3; trivial. *)
Case "<-".
    intro H. induction H; simpl;
    subst; try reflexivity; try assumption.
    destruct (eq_nat_dec I I); try reflexivity. apply ex_falso_quodlibet; auto.
    destruct (eq_nat_dec I N); try reflexivity. apply ex_falso_quodlibet; auto.
    subst; unfold lt in H; eapply le_Sn_n; apply H.
    destruct (le_lt_dec I N); try reflexivity.
    apply ex_falso_quodlibet. eapply lt_not_le. apply H; assumption. assumption.
    destruct (eq_nat_dec I N). apply ex_falso_quodlibet; subst. eapply gt_irrefl.
    apply H.
    destruct (le_lt_dec I N); try reflexivity. unfold gt in H.
    apply ex_falso_quodlibet. eapply lt_asym. apply H. trivial.
Qed.


(* Type in Coercion Substitution *)

Fixpoint subst_ty_in_cn_fix (X:nat) (U:ty) (c:cn) : cn :=
  match c with
    | CAxiom ks T T' =>
      CAxiom ks (subst_type_in_type_fix (length ks + X) (tshift 0 U) T)
                (subst_type_in_type_fix (length ks + X) (tshift 0 U) T')
    | CVar y       => CVar y                           
    | CRefl T      => CRefl ([X := U] T)
    | CSym c       => CSym (subst_ty_in_cn_fix X U c)
    | CTrans c1 c2 => CTrans (subst_ty_in_cn_fix X U c1)
                             (subst_ty_in_cn_fix X U c2)
    | CApp c1 c2 => CApp (subst_ty_in_cn_fix X U c1)
      (subst_ty_in_cn_fix X U c2)
    | CNth n c     => CNth n (subst_ty_in_cn_fix X U c)
    | CTAbs k c      => CTAbs k (subst_ty_in_cn_fix (S X) (tshift 0 U) c)
    | CTApp c T    => CTApp (subst_ty_in_cn_fix X U c) ([X := U] T)
  end.

Instance subst_ty_cn : Subst nat ty cn := {
  do_subst := subst_ty_in_cn_fix
}.

Inductive subst_ty_in_cn (T:ty) (X:nat) : cn -> cn -> Prop :=
  | stc_var : forall x,
                subst_ty_in_cn T X (CVar x) (CVar x)
  | stc_axiom : forall ks t u t' u',
      subst_type_in_type (tshift 0 T) (length ks + X) t t' ->
      subst_type_in_type (tshift 0 T) (length ks + X) u u' ->
      subst_ty_in_cn T X (CAxiom ks t u) (CAxiom ks t' u')
  | stc_refl : forall U U',
      subst_type_in_type T X U U' ->
      subst_ty_in_cn T X (CRefl U) (CRefl U')
  | stc_sym : forall c c',
      subst_ty_in_cn T X c c' ->
      subst_ty_in_cn T X (CSym c) (CSym c')
  | stc_trans : forall c1 c1' c2 c2',
      subst_ty_in_cn T X c1 c1' ->
      subst_ty_in_cn T X c2 c2' ->
      subst_ty_in_cn T X (CTrans c1 c2) (CTrans c1' c2')
  | stc_caapp : forall c1 c1' c2 c2',
      subst_ty_in_cn T X c1 c1' ->
      subst_ty_in_cn T X c2 c2' ->
      subst_ty_in_cn T X (CApp c1 c2) (CApp c1' c2')
  | stc_nth : forall c c' n,
      subst_ty_in_cn T X c c' ->
      subst_ty_in_cn T X (CNth n c) (CNth n c')
  | stc_tabs : forall c c' k,
      subst_ty_in_cn (tshift 0 T) (S X) c c' ->
      subst_ty_in_cn T X (CTAbs k c) (CTAbs k c')
  | stc_tapp : forall c c' U V,
      subst_ty_in_cn T X c c'    ->
      subst_type_in_type T X U V ->
      subst_ty_in_cn T X (CTApp c U) (CTApp c' V).


Lemma subst_ty_in_cn_correct : forall U X c c',
  [X := U]c = c' <-> subst_ty_in_cn U X c c'.
Proof.
  intros. split.
  Case "->".
    generalize dependent c'. generalize dependent X.
    generalize dependent U.
    induction c; intros; simpl in H;
      try (subst; constructor; apply IHc; trivial);
      try (rewrite <- H; constructor);
      try (apply IHc; trivial);
      try (apply IHc1; trivial);
      try (apply IHc2; trivial);
      try (apply IHc3; trivial);
      try (apply subst_type_in_type_correct; trivial).
    simpl.
  Case "<-".
    intro H. induction H; simpl;
    subst; try reflexivity; try assumption;
    try (apply subst_type_in_type_correct in H; subst; trivial);
    try (apply subst_type_in_type_correct in H0; subst; trivial).
Qed.


(* Type in Term Substitution *)

Fixpoint subst_type_fix (X:nat) (T:ty) (t:tm) : tm :=
  match t with
  | tvar x =>
      tvar x
  | tabs T' t1 => 
      tabs ([X := T] T') (subst_type_fix X T t1) 
  | tapp t1 t2 => 
      tapp (subst_type_fix X T t1) (subst_type_fix X T t2)
  | ttabs k t1 =>
      ttabs k (subst_type_fix (X+1) (tshift 0 T) t1) 
  | ttapp t' T' =>
      ttapp (subst_type_fix X T t') ([X := T] T')
  | tcabs T1 T2 t1 =>
      tcabs ([X:=T]T1) ([X:=T]T2) (subst_type_fix X T t1)
  | tcapp t1 c2 =>
      tcapp (subst_type_fix X T t1) ([X := T] c2)
  | tcoerce t1 c2 =>
      tcoerce (subst_type_fix X T t1) ([X := T] c2)
  end.

Instance subst_ty_tm : Subst nat ty tm := {
  do_subst := subst_type_fix
}.

Inductive subst_type (P:ty) (I:nat) : tm -> tm -> Prop := 
  | st_var : forall x,
      subst_type P I (tvar x) (tvar x)
  | st_tabs : forall T1 T2 t t',
      subst_type P I t t' ->
      subst_type_in_type P I T1 T2 ->
      subst_type P I (tabs T1 t) (tabs T2 t')
  | st_tapp : forall t1 t2 t1' t2',
      subst_type P I t1 t1' ->
      subst_type P I t2 t2' ->
      subst_type P I (tapp t1 t2) (tapp t1' t2')
  | st_ttabs : forall t t' k,
      subst_type (tshift 0 P) (I+1) t t' ->
      subst_type P I (ttabs k t) (ttabs k t')
  | st_ttapp : forall t t' T1 T2,
      subst_type P I t t' ->
      subst_type_in_type P I T1 T2 ->
      subst_type P I (ttapp t T1) (ttapp t' T2)
  | st_tcabs : forall t t' U1 U2 V1 V2,
      subst_type P I t t'          ->
      subst_type_in_type P I U1 V1 ->
      subst_type_in_type P I U2 V2 ->
      subst_type P I (tcabs U1 U2 t) (tcabs V1 V2 t')
  | st_tcapp : forall t t' c c',
      subst_type P I t t'     ->
      subst_ty_in_cn P I c c' ->
      subst_type P I (tcapp t c) (tcapp t' c')
  | st_tcoerce : forall t t' c c',
      subst_type P I t t'     ->
      subst_ty_in_cn P I c c' ->
      subst_type P I (tcoerce t c) (tcoerce t' c').

Hint Constructors subst_type.

Theorem subst_type_correct : forall P I t t',
  [I := P] t = t' <-> subst_type P I t t'.
Proof.

  intros. split.
  Case "->".
    generalize dependent I. generalize dependent P.
    generalize dependent t'.
    induction t; intros t' P I H; simpl in H;
      try (rewrite <- H; constructor; apply IHt; reflexivity).
    SCase "t = tapp t1 t2".
      rewrite <- H. constructor.
      apply IHt1. reflexivity.
      apply IHt2. reflexivity.
    SCase "t = tabs T t0".
      rewrite <- H. constructor.
      apply IHt. reflexivity.
      apply subst_type_in_type_correct. reflexivity.
    SCase "t = ttapp".
      subst. constructor. apply IHt. reflexivity.
      apply subst_type_in_type_correct. reflexivity.
    SCase "t = tcapp".
      subst. constructor. apply IHt. reflexivity.
      apply subst_ty_in_cn_correct. reflexivity.
    SCase "t = tcabs".
      subst. constructor. apply IHt. reflexivity.
      apply subst_type_in_type_correct; trivial.
      apply subst_type_in_type_correct; trivial.
    SCase "t = tcoerce".
      subst. constructor. apply IHt. trivial.
      apply subst_ty_in_cn_correct. reflexivity.
  Case "<-".
    intro H. induction H; simpl;
    subst; try reflexivity; try assumption;
    try (apply subst_type_in_type_correct in H0;
         unfold do_subst in H0; unfold subst_ty_ty in H0;
         rewrite -> H0; reflexivity);
    try (apply subst_ty_in_cn_correct in H0;
         unfold do_subst in H0; unfold subst_ty_cn in H0;
         rewrite -> H0; reflexivity).
    apply subst_type_in_type_correct in H0.
    apply subst_type_in_type_correct in H1. subst. trivial.
Qed.


(** [] *)


(* Type in Term Substitution *)

Fixpoint subst_cn_in_tm_fix (x:nat) (c:cn) (t:tm) : tm :=
  match t with
  | tvar x =>
      tvar x
  | tabs T t1 => 
      tabs T (subst_cn_in_tm_fix x c t1) 
  | tapp t1 t2 => 
      tapp (subst_cn_in_tm_fix x c t1) (subst_cn_in_tm_fix x c t2)
  | ttabs k t1 =>
      ttabs k (subst_cn_in_tm_fix x (cshift_typ 0 c) t1) 
  | ttapp t' T' =>
      ttapp (subst_cn_in_tm_fix x c t') T'
  | tcabs T1 T2 t1 =>
      tcabs T1 T2 (subst_cn_in_tm_fix (S x) (cshift 0 c) t1)
  | tcapp t1 c2 =>
      tcapp (subst_cn_in_tm_fix x c t1) ([x := c] c2)
  | tcoerce t1 c2 =>
      tcoerce (subst_cn_in_tm_fix x c t1) ([x := c] c2)
  end.

Instance subst_cn_tm : Subst nat cn tm := {
  do_subst := subst_cn_in_tm_fix
}.

Inductive subst_cn_in_tm (c:cn) (x:nat) : tm -> tm -> Prop := 
  | sct_var : forall y,
      subst_cn_in_tm c x (tvar y) (tvar y)
  | sct_tabs : forall T t t',
      subst_cn_in_tm c x t t'          ->
      subst_cn_in_tm c x (tabs T t) (tabs T t')
  | sct_tapp : forall t1 t2 t1' t2',
      subst_cn_in_tm c x t1 t1' ->
      subst_cn_in_tm c x t2 t2' ->
      subst_cn_in_tm c x (tapp t1 t2) (tapp t1' t2')
  | sct_ttabs : forall t t' k,
      subst_cn_in_tm (cshift_typ 0 c) x t t' ->
      subst_cn_in_tm c x (ttabs k t) (ttabs k t')
  | sct_ttapp : forall t t' T,
      subst_cn_in_tm c x t t' ->
      subst_cn_in_tm c x (ttapp t T) (ttapp t' T)
  | sct_tcabs : forall t t' T1 T2,
      subst_cn_in_tm (cshift 0 c) (S x) t t' ->
      subst_cn_in_tm c x (tcabs T1 T2 t) (tcabs T1 T2 t')
  | sct_tcapp : forall t t' d d',
      subst_cn_in_tm c x t t'     ->
      subst_coercion c x d d' ->
      subst_cn_in_tm c x (tcapp t d) (tcapp t' d')
  | sct_tcoerce : forall t t' d d',
      subst_cn_in_tm c x t t'     ->
      subst_coercion c x d d' ->
      subst_cn_in_tm c x (tcoerce t d) (tcoerce t' d').

Hint Constructors subst_type.

Theorem subst_cn_in_tm_correct : forall c x t t',
  [x := c] t = t' <-> subst_cn_in_tm c x t t'.
Proof.
  intros. split.
  Case "->".
    generalize dependent x. generalize dependent c.
    generalize dependent t'.
    induction t; intros; simpl in H;
      try (rewrite <- H; try constructor; apply IHt; reflexivity).
    SCase "t = tapp t1 t2".
      rewrite <- H. constructor.
      apply IHt1. reflexivity.
      apply IHt2. reflexivity.
     SCase "t = tcapp".
      subst. constructor. apply IHt. reflexivity.
      apply subst_coercion_correct. reflexivity.
    SCase "t = tcoerce".
      subst. constructor. apply IHt. reflexivity.
      apply subst_coercion_correct. reflexivity.
  Case "<-".
    intro H. induction H; simpl;
    subst; try reflexivity; try assumption;
    try (apply subst_coercion_correct in H0;
         unfold do_subst in H0; unfold subst_cn in H0;
         rewrite -> H0; reflexivity).
Qed.

(* ####################################################### *)  
(* ** (Type variable) Shifting and substitution properties *)


(* The next two tactics come from the POPL paper *)
 Ltac tvar_case :=
   unfold tshift; unfold do_subst; fold tshift; fold do_subst;
   match goal with
   | |- ?x =>
       match x with
       | context [le_gt_dec ?n ?n'] =>
           case (le_gt_dec n n')
       | context C [(lt_eq_lt_dec ?n ?n')] =>
           case (lt_eq_lt_dec n n'); [intro s; case s; clear s | idtac ]
       end
   end.

 Ltac common_cases n T :=
   simpl; generalize n; clear n; induction T; intros n''; intros;
     [ repeat tvar_case;
       simpl; trivial; try (intros; apply f_equal with (f := tvar); omega);
       try (intros; assert False; [ omega | contradiction ])
     | simpl; trivial
     | simpl; try (apply f_equal2 with (f := TApp); trivial)
     | simpl ].

 Lemma subst_shift_same : forall X T U,
   T = [X := U] (tshift X T).
 Proof.
   intros. generalize dependent X. generalize dependent U.
   induction T; intros.
     simpl. destruct (le_gt_dec X n).
       destruct (eq_nat_dec X (S n)).
         omega.
       destruct (le_lt_dec X (S n)). assert (n = S n - 1) by omega. auto.
         omega.
       destruct (eq_nat_dec X n).
         omega.
         destruct (le_lt_dec X n). omega. trivial.
     simpl. trivial.
     simpl. simpl in IHT1. rewrite <- IHT1. simpl in IHT2; rewrite <- IHT2. trivial.
     simpl. simpl in IHT. assert (S X = X + 1) by omega. rewrite H.
       rewrite <- IHT. trivial.
 Qed.

 Lemma tshift_tshift_prop : forall X Y T,
   tshift X (tshift (X + Y) T) = tshift (1 + X + Y) (tshift X T).
 Proof.
   intros. common_cases X T.
   rewrite IHT.  trivial. 
 Qed.

Lemma tshift_subst_prop_2 : forall n n' T T',
  (tshift (n + n') ([n := T'] T)) =
  ([n := (tshift (n + n') T')] (tshift (1 + n + n') T)).
Proof.
  intros. generalize dependent T'. common_cases n T. intros.
  destruct (eq_nat_dec n'' n). omega.
    destruct (le_lt_dec n'' n).
      destruct (eq_nat_dec n'' (S n)).
        omega.
        destruct (le_lt_dec n'' (S n)).
          simpl. destruct (le_gt_dec (n'' + n') (n - 1)).
          assert (S (n - 1) = n - 0) by omega. rewrite H. trivial.
          omega.
        omega.
      omega.
    intros.
    destruct (eq_nat_dec n'' n).
      trivial.
      destruct (le_lt_dec n'' n).
        simpl. destruct (le_gt_dec (n'' + n') (n - 1)).
          omega.
          trivial.
        simpl.
      destruct (le_gt_dec (n'' + n') n).
        omega.
        trivial.
    apply f_equal. assert (n'' + n' = 0 + (n'' + n')) by trivial.
    rewrite H. rewrite tshift_tshift_prop. simpl.
    assert (S (n'' + n') = (n'' + 1) + n') by omega.
    rewrite H0. apply IHT.
Qed.


 Lemma tshift_subst_prop : forall X Y T U,
   tshift X ([X + Y := U] T) =
   [S (X + Y) := tshift X U] (tshift X T).
 Proof.
   intros. generalize dependent U. common_cases X T. intros.
   simpl. destruct (eq_nat_dec (n'' + Y) n). trivial.
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
     trivial.
     (*
     destruct (Arith.EqNat.Beq_nat (n'' + Y) n). omega. trivial.
     apply f_equal.
     *)
     assert (n'' + Y <> n) by omega.
     (* I can't find the proper lemma, so the following proof is a quick, dirty fix *)
     remember (Nat.eq_dec (n'' + Y) n) as peq.
     destruct peq ; [contradiction | trivial].
     assert (tshift 0 (tshift (0 + n'') U) = tshift (1 + 0 + n'') (tshift 0 U))
       as H by (apply tshift_tshift_prop) ;
     simpl in H ; rewrite H ; clear H.
     assert (n'' + Y + 1 = (S n'') + Y) as _H by omega ; rewrite _H ; clear _H.
     rewrite IHT. trivial. 
 Qed.

 Lemma tsubst_tsubst_prop : forall X Y (T U V : ty),
   [X + Y := V] ([X := U] T) =
   [X := [X + Y := V] U] ([1 + X + Y := tshift X V] T).
 Proof.
   intros X Y T. common_cases X T.

   destruct (eq_nat_dec n'' n). 
   destruct n. simpl. destruct (eq_nat_dec n'' 0).
   trivial. omega.
   unfold sumbool_rec. unfold sumbool_rect.
   destruct (eq_nat_dec (n'' + Y) n). omega.
   destruct (le_lt_dec (n'' + Y) n). omega. simpl.
   destruct (eq_nat_dec n'' (S n)).
   trivial. omega.
   destruct (le_lt_dec n'' n). simpl.
   destruct (eq_nat_dec (n'' + Y) (n - 1)). destruct n.
   omega. unfold sumbool_rec. unfold sumbool_rect.
   destruct (eq_nat_dec (n'' + Y) n). subst.
   apply subst_shift_same. simpl. omega.
   destruct (le_lt_dec (n'' + Y) (n - 1)).
   unfold sumbool_rec. unfold sumbool_rect. destruct n. simpl.
   omega. simpl. destruct (eq_nat_dec (n'' + Y) n). omega.
   simpl. destruct (le_lt_dec (n'' + Y) n). simpl.
   destruct (eq_nat_dec n'' (n - 0) ). omega. simpl.
   destruct (le_lt_dec n'' (n - 0)). trivial. omega. omega.
   destruct (match n as n2 return ({S (n'' + Y) = n2} + {S (n'' + Y) <> n2}) with
               | 0 => right (not_eq_sym (O_S (n'' + Y)))
               | S m =>
                 sumbool_rec
                   (fun _ : {n'' + Y = m} + {n'' + Y <> m} =>
                      {S (n'' + Y) = S m} + {S (n'' + Y) <> S m})
                   (fun a : n'' + Y = m => left (f_equal S a))
                   (fun b : n'' + Y <> m => right (not_eq_S (n'' + Y) m b))
                   (eq_nat_dec (n'' + Y) m)
             end).
   omega. unfold sumbool_rec. unfold sumbool_rect. destruct n. omega.
   destruct (le_lt_dec (n'' + Y) n). omega. simpl.
   destruct (eq_nat_dec n'' (S n)). omega.
   destruct (eq_nat_dec (n'' + Y) n). omega. simpl.
   destruct (eq_nat_dec n'' (S n)). omega.
   destruct (le_lt_dec n'' (S n)). trivial. omega.

   simpl. 
   destruct (eq_nat_dec (n'' + Y) n). unfold sumbool_rec. unfold sumbool_rect.
   destruct n. simpl. destruct (eq_nat_dec n'' 0). omega.
   destruct (le_lt_dec n'' 0). omega. omega. simpl. omega.
   destruct (le_lt_dec (n'' + Y) n). omega.
   unfold sumbool_rec. unfold sumbool_rect. destruct n. simpl.
   destruct (eq_nat_dec n'' 0). omega.
   destruct (le_lt_dec n'' 0). trivial. trivial. 
   destruct (eq_nat_dec (n'' + Y) n). omega.
   destruct (le_lt_dec (n'' + Y) n). omega. simpl.
   destruct (eq_nat_dec n'' (S n)). omega.
   destruct (le_lt_dec n'' (S n)). omega. trivial.

   assert (n'' + Y = 0 + (n'' + Y)) by trivial. rewrite H. clear H. 
   rewrite tshift_subst_prop. simpl.
   assert (n'' = 0 + n'') by trivial. rewrite H. clear H.
   rewrite tshift_tshift_prop. simpl. 
   assert (n'' + Y + 1 = n'' + 1 + Y) by omega. rewrite H. clear H.
   rewrite IHT.
   assert (n'' + 1 = S n'') by omega. rewrite H. clear H.
   trivial.
Qed.

