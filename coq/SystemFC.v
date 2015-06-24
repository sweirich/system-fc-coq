
(** * System FC **)
Require Export SfLib.


(* ###################################################################### *)
(** ** Syntax *)

Module SYSTEMFC.

(* ################################### *)
(** *** Types *)

Inductive kind : Type :=
 | KStar : kind
 | KArrow : kind -> kind -> kind.
  
Inductive tycon : Type :=
| TArrow  : tycon
| TEq     : kind -> tycon
| TData   : nat -> tycon.
  
Inductive ty : Type := 
| TVar   : nat -> ty
| TCon   : tycon -> ty
| TApp   : ty -> ty -> ty
| TUniv  : kind -> ty -> ty.


(* ################################### *)
(** *** Coercions *)

Inductive cn : Type :=
  | CAxiom   : list kind -> ty -> ty -> cn
  | CVar     : nat -> cn
  | CRefl    : ty -> cn
  | CSym     : cn -> cn
  | CTrans   : cn -> cn -> cn
  | CApp     : cn -> cn -> cn
  | CNth     : nat -> cn -> cn
  | CTAbs    : kind -> cn -> cn
  | CTApp    : cn -> ty -> cn.

Tactic Notation "c_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "CAxiom" 
  | Case_aux c "CVar"   | Case_aux c "CRefl"
  | Case_aux c "CSym"   | Case_aux c "CTrans"
  | Case_aux c "CApp"  (* | Case_aux c "CTCoerce" *)
  | Case_aux c "CNth"
  | Case_aux c "CTAbs"  | Case_aux c "CTApp" ].


(* ################################### *)
(** *** Terms *)

Inductive tm : Type :=
  | tvar    : nat -> tm
  | tapp    : tm -> tm -> tm
  | tabs    : ty -> tm -> tm
  | ttapp   : tm -> ty -> tm
  | ttabs   : kind -> tm -> tm
  | tcapp   : tm -> cn -> tm
  | tcabs   : ty -> ty -> tm -> tm
  | tcoerce : tm -> cn -> tm.

Tactic Notation "t_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tvar"  | Case_aux c "tapp" 
  | Case_aux c "tabs"  | Case_aux c "ttapp" 
  | Case_aux c "ttabs" | Case_aux c "tcapp"
  | Case_aux c "tcabs" | Case_aux c "tcoerce" ].


(* ################################### *)
(** *** Values *)

Inductive uncoerced_value : tm -> Prop :=
  | uv_abs : forall T t,
      uncoerced_value (tabs T t)
  | uv_tabs : forall t k,
      uncoerced_value (ttabs k t)
  | uv_cabs : forall t T1 T2,
      uncoerced_value (tcabs T1 T2 t).

Hint Constructors uncoerced_value.

Inductive value : tm -> Prop :=
  | v_uncoerced : forall t,
      uncoerced_value t ->
      value t
  | v_coerced : forall t c,
      uncoerced_value t ->
      value (tcoerce t c).

Hint Constructors value.


End SYSTEMFC.