(** * Shifting in System FC *)
Require Import Omega.
Require Export SystemFC.

Module SHIFTING.
Import SYSTEMFC.

(* ################################### *)
(** *** Types *)

Class ShiftTyp (X : Type) := {
  shift_typ : nat -> X -> X                                     
}.

Class ShiftCoercion (X : Type) := {
  shift_cn : nat -> X -> X                                     
}.


(* Types in Types *)
Fixpoint tshift (X : nat) (T : ty) : ty :=
  match T with
    | TVar Y        => TVar (if le_gt_dec X Y then 1 + Y else Y)
    | TCon Y        => TCon Y
    | TApp T1 T2    => TApp (tshift X T1) (tshift X T2)
    | TUniv K T2    => TUniv K (tshift (1 + X) T2)
  end.

Instance shift_type_type : ShiftTyp ty := {
   shift_typ := tshift
}.                                                      

(* ################################### *)
(** *** Coercions *)

(* Coercions in Coercions *)
Fixpoint cshift (X : nat) (c : cn) : cn :=
  match c with
  | CAxiom ks t u     => CAxiom ks t u
  | CVar Y            => CVar (if le_gt_dec X Y then 1 + Y else Y)
  | CRefl T           => CRefl T
  | CSym c            => CSym (cshift X c)
  | CTrans c1 c2      => CTrans (cshift X c1) (cshift X c2)
  | CApp c1 c2        => CApp (cshift X c1) (cshift X c2)
  | CNth n c          => CNth n (cshift X c)
  | CTAbs k c         => CTAbs k (cshift X c)
  | CTApp c T         => CTApp (cshift X c) T
  end.

(* Types in Coercions *)
Fixpoint cshift_typ (X : nat) (c : cn) : cn :=
  match c with
  | CAxiom ks t u     => CAxiom ks (tshift (length ks + X) t)
                                   (tshift (length ks + X) u)
  | CVar Y            => CVar Y
  | CRefl T           => CRefl (tshift X T)
  | CSym c            => CSym (cshift_typ X c)
  | CTrans c1 c2      => CTrans (cshift_typ X c1) (cshift_typ X c2)
  | CApp c1 c2        => CApp (cshift_typ X c1) (cshift_typ X c2)
  | CNth n c          => CNth n (cshift_typ X c)
  | CTAbs k c         => CTAbs k (cshift_typ (S X) c)
  | CTApp c T         => CTApp (cshift_typ X c) (tshift X T)
  end.

Instance shift_cn_cn : ShiftCoercion cn := {
  shift_cn := cshift
}.                      
Instance shift_typ_cn : ShiftTyp cn := {
   shift_typ := cshift_typ
}.                                                      


(* ################################### *)
(** *** Terms *)

(* Terms in Terms *)
Fixpoint shift (x:nat) (t:tm) : tm :=
  match t with
    | tvar y         => tvar (if le_gt_dec x y then S y else y)
    | tabs T1 t2     => tabs T1 (shift (S x) t2)
    | tapp t1 t2     => tapp (shift x t1) (shift x t2)
    | ttabs k t2     => ttabs k (shift x t2)
    | ttapp t1 T2    => ttapp (shift x t1) T2
    | tcapp t1 c2    => tcapp (shift x t1) c2
    | tcabs T1 T2 t2 => tcabs T1 T2 (shift x t2)
    | tcoerce t c    => tcoerce (shift x t) c
  end.

(* Coercions in Terms *)
Fixpoint tshift_cn (X : nat) (t : tm) : tm :=
  match t with
    | tvar y         => tvar y
    | tabs T1 t2     => tabs T1 (tshift_cn X t2)
    | tapp t1 t2     => tapp (tshift_cn X t1) (tshift_cn X t2)
    | ttabs k t2     => ttabs k (tshift_cn X t2)
    | ttapp t1 T2    => ttapp (tshift_cn X t1) T2
    | tcapp t1 c2    => tcapp (tshift_cn X t1) (cshift X c2)
    | tcabs T1 T2 t2 => tcabs T1 T2 (tshift_cn (S X) t2)
    | tcoerce t c    => tcoerce (tshift_cn X t) (cshift X c)
  end.

(* Types in Terms *)
Fixpoint tshift_typ (X : nat) (t : tm) {struct t} : tm :=
  match t with
    | tvar y         => tvar y
    | tabs T1 t2     => tabs (tshift X T1) (tshift_typ X t2)
    | tapp t1 t2     => tapp (tshift_typ X t1) (tshift_typ X t2)
    | ttabs k t2     => ttabs k (tshift_typ (1 + X) t2)
    | ttapp t1 T2    => ttapp (tshift_typ X t1) (tshift X T2)
    | tcapp t1 c2    => tcapp (tshift_typ X t1) (cshift_typ X c2)
    | tcabs T1 T2 t2 => tcabs (tshift X T1) (tshift X T2) (tshift_typ X t2)
    | tcoerce t1 c2  => tcoerce (tshift_typ X t1) (cshift_typ X c2)
  end.


Instance shift_cn_tm : ShiftCoercion tm := {
  shift_cn := tshift_cn
}.                      
Instance shift_typ_tm : ShiftTyp tm := {
   shift_typ := tshift_typ
}.                                                      

End SHIFTING.