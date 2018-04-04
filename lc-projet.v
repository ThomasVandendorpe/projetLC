Section tbool.

  (*
   *    I Logique à trois valeurs
   *)
  
  Variable T: Set.
  
  (* V, F et P en Coq *)
  Definition tbool := T -> T -> T -> T.
  Definition tv : tbool := fun x y z => x.
  Definition tf : tbool := fun x y z => y.
  Definition tp : tbool := fun x y z => z.

  (* CONDITION *)
  (* Les tbool sont des fonctions a 3 paramètres qui renvoient l'un de ces paramètre(le premier pour vrai, le second pour faux et le troisième pour peut-être), le if s'obtient en appliquant un tbool à trois arguments*)
  Definition tif : tbool -> T -> T -> T -> T := fun tb x y z=> tb x y z.
  
  Variable m n o : T.
  Fact tif_v : tif tv m n o = m.
  Proof.
    cbv delta [tif].
    cbv beta.
    cbv delta [tv].
    cbv beta.
    reflexivity.
  Qed.
  Fact tif_f : tif tf m n o = n. Proof. reflexivity. Qed.
  Fact tif_p : tif tp m n o = o. Proof. reflexivity. Qed.

  (* NEGATION *)
  (* V -> F
     F -> V
     P -> P
     On peut donc traduire la négation du tbool b de la forme 'Lambda x y z . r' ou r est soit x, soit y, soit z
     Par:
       SI b vaut tv (b renvoie le 1er argument ie. r=x) ALORS ON DOIT RENVOYER y
       SINON si b vaut tf (b renvoie le 2nd argument ie. r=y) ALORS ON DOIT RENVOYER x
       SINON (b renvoie le 3eme argument ie. r=z) ON DOIT RENVOYER z 
   *)
  Definition tnot : tbool -> tbool := fun tb => fun x y z => tb y x z. 
    
  Fact tnot_v : tnot tv = tf.
  Proof.
    cbv delta [tnot].
    cbv beta.
    cbv delta [tif].
    cbv beta.
    cbv delta [tv].
    cbv delta [tf].
    cbv beta.
    reflexivity.
  Qed.
  Fact tnot_f : tnot tf = tv. Proof. reflexivity. Qed.
  Fact tnot_p : tnot tp = tp. Proof. reflexivity. Qed.

  (* CONJONCTION *)
  (* 
    Soit deux tbool a et b. La conjonction de ces deux tbool sera un tbool c de la forme 'Lambda x y z . r'. 
    Que vaut r?
    On distingue plusieurs cas:
    -a vaut tv:
        -c sera égal à b, donc r vaut b x y z
    -a vaut tf:
        -c sera égal à tf, donc r vaut y
    -a vaut tp:
        -si b vaut tv: r vaut z
        -si b vaut tf: r vaut y
        -si b vaut tp: r vaut z
   *)
  Definition tand : tbool -> tbool -> tbool := fun a b => fun x y z => a (b x y z) y (b z y z).

  Fact tand_vv : tand tv tv = tv. Proof. reflexivity. Qed.
  Fact tand_vf : tand tv tf = tf. Proof. reflexivity. Qed.
  Fact tand_vp : tand tv tp = tp. Proof. reflexivity. Qed.
  Fact tand_fv : tand tf tv = tf. Proof. reflexivity. Qed.
  Fact tand_ff : tand tf tf = tf. Proof. reflexivity. Qed.
  Fact tand_fp : tand tf tp = tf. Proof. reflexivity. Qed.
  Fact tand_pv : tand tp tv = tp. Proof. reflexivity. Qed.
  Fact tand_pf : tand tp tf = tf. Proof. reflexivity. Qed.
  Fact tand_pp : tand tp tp = tp. Proof. reflexivity. Qed.

  (* DISJONCTION *)
  (* 
    Soit deux tbool a et b. La disjonction de ces deux tbool sera un tbool c de la forme 'Lambda x y z . r'. 
    Que vaut r?
    On distingue plusieurs cas:
    -a vaut tv:
        -c sera égal à tv, donc r vaut x
    -a vaut tf:
        -c sera égal à b, donc r vaut b x y z
    -a vaut tp:
        -si b vaut tv: r vaut x
        -si b vaut tf: r vaut z
        -si b vaut tp: r vaut z
   *)
  Definition tor : tbool -> tbool -> tbool := fun a b => fun x y z => a x (b x y z) (b x z z).

  Fact tor_vv : tor tv tv = tv. Proof. reflexivity. Qed.
  Fact tor_vf : tor tv tf = tv. Proof. reflexivity. Qed.
  Fact tor_vp : tor tv tp = tv. Proof. reflexivity. Qed.
  Fact tor_fv : tor tf tv = tv. Proof. reflexivity. Qed.
  Fact tor_ff : tor tf tf = tf. Proof. reflexivity. Qed.
  Fact tor_fp : tor tf tp = tp. Proof. reflexivity. Qed.
  Fact tor_pv : tor tp tv = tv. Proof. reflexivity. Qed.
  Fact tor_pf : tor tp tf = tp. Proof. reflexivity. Qed.
  Fact tor_pp : tor tp tp = tp. Proof. reflexivity. Qed.
  
End tbool.

(*
 *    II Programmation en Lambda-calcul polymorphe
 *)

(* 2.1 Type de l'identite polymorphe *)
(* 1. *)
Definition tid : Set := forall T: Set, T -> T.
Definition id : tid := fun T:Set => fun x:T => x.

(*Exemple :*)
Compute id nat 3 .
Compute id nat 0.
Compute id bool true.
Compute id bool false.

(* 2. *)
Definition nbtrue1 := fun b =>
                        match b with true => 1 | false => 0 end.
Definition nbfalse1 := fun b =>
                         match b with false => 1 | true => 0 end.
Compute id (bool->nat) nbtrue1.
Compute id (bool->nat) nbfalse1.

(* 3. *)
Compute id (tid) id.

(* 4. *)
Theorem th_id : forall T: Set, forall x: T, id T x = x.
Proof.
  intros.
  cbv delta [id].
  cbv beta.
  reflexivity.
Qed.

(* 2.2 Booléens avec typage polymorphe *)
(* 1. *)
Definition pbool : Set := forall T:Set, T -> T -> T.
Definition ptr : pbool := fun T:Set => fun x y => x.
Definition pfa : pbool := fun T:Set => fun x y => y.

(* 2 *)
Definition pneg : pbool -> pbool := fun b:pbool => fun T => fun x y => b T y x.
Compute pneg ptr.
Compute pneg pfa.

Definition pif : forall T:Set, pbool -> T -> T -> T := fun T => fun b:pbool => fun x y => b T x y.
Compute pif nat ptr 1 2.
Compute pif nat pfa 1 2.

Definition pneg2 : pbool -> pbool := fun b:pbool => pif pbool b ptr pfa.
Compute pneg2 ptr.
Compute pneg2 pfa.

(* 3. *)
(* CONJONCTION *)
Definition pand : pbool -> pbool -> pbool := fun a b : pbool => a pbool b pfa.
Fact pand_vv: pand ptr ptr = ptr. Proof. reflexivity. Qed.
Fact pand_vf: pand ptr pfa = pfa. Proof. reflexivity. Qed.
Fact pand_fv: pand pfa ptr = pfa. Proof. reflexivity. Qed.
Fact pand_ff: pand pfa pfa = pfa. Proof. reflexivity. Qed.

(* DISJONCTION *)
Definition por : pbool -> pbool -> pbool := fun a b : pbool => a pbool ptr b.
Fact por_vv: por ptr ptr = ptr. Proof. reflexivity. Qed.
Fact por_vf: por ptr pfa = ptr. Proof. reflexivity. Qed.
Fact por_fv: por pfa ptr = ptr. Proof. reflexivity. Qed.
Fact por_ff: por pfa pfa = pfa. Proof. reflexivity. Qed.

(* 4. *)
Definition f4 : pbool -> nat := fun b:pbool => b nat 3 5.
Compute f4 ptr.
Compute f4 pfa.

(* 5. *)
Definition f5 : pbool -> (pbool -> pbool):= fun b:pbool => b pbool b.

Check f5.
(* f5 est une fonction pbool -> pbool -> pbool *)
(* On teste f5 pour les différentes valeurs possible: *)
Compute f5 ptr ptr. (*ptr ptr -> ptr*)
Compute f5 ptr pfa. (*ptr pfa -> ptr*)
Compute f5 pfa ptr. (*pfa ptr -> ptr*)
Compute f5 pfa pfa. (*pfa pfa -> pfa*)
(* On remarque que f5 a la même table de vérité que por *)

(* Prouvons l'égalité entre f5 et por à l'aide d'un type énuméré *)
(* Definition d’un type enumerant les numeros *)
Inductive pbool_num : Set := bnt | bnf.

(* Fonction d’association entre numero et booleen *)
Definition cbool_of := fun n =>
match n with
| bnt => ptr
| bnf => pfa
end.

Lemma f5_por: forall a b: pbool_num, f5 (cbool_of a) (cbool_of b) = por (cbool_of a) (cbool_of b). 
Proof.
  intros a b.
  -destruct a.
   + unfold cbool_of. reflexivity.
   + reflexivity.
Qed.

(* 2.3 Logique à trois valeurs *)

(* V, F et P en typage polymorphe *)
Definition ptbool : Set := forall T:Set, T -> T -> T -> T.
Definition ptv : ptbool := fun T:Set => fun x y z => x.
Definition ptf : ptbool := fun T:Set => fun x y z => y.
Definition ptp : ptbool := fun T:Set => fun x y z => z.

(* CONDITION *)
Definition ptif : forall T:Set, ptbool -> T -> T -> T -> T := fun T => fun b x y z=> b T x y z.

Fact ptif_v : ptif nat ptv 1 2 3 = 1.
Proof.
  cbv delta [ptif].
  cbv beta.
  cbv delta [ptv].
  cbv beta.
  reflexivity.
Qed.
Fact ptif_f : ptif nat ptf 1 2 3 = 2. Proof. reflexivity. Qed.
Fact ptif_p : ptif nat ptp 1 2 3 = 3. Proof. reflexivity. Qed.

(* NEGATION *)
Definition ptnot : ptbool -> ptbool := fun b => fun T => fun x y z => b T y x z. 

Fact ptnot_v : ptnot ptv = ptf.
Proof.
  cbv delta [ptnot].
  cbv beta.
  cbv delta [ptif].
  cbv beta.
  cbv delta [ptv].
  cbv delta [ptf].
  cbv beta.
  reflexivity.
Qed.
Fact ptnot_f : ptnot ptf = ptv. Proof. reflexivity. Qed.
Fact ptnot_p : ptnot ptp = ptp. Proof. reflexivity. Qed.

(* CONJONCTION *)
Definition ptand : ptbool -> ptbool -> ptbool := fun a b => fun T => fun x y z => a T (b T x y z) y (b T z y z).

Fact ptand_vv : ptand tv tv = tv. Proof. reflexivity. Qed.
Fact ptand_vf : ptand tv tf = tf. Proof. reflexivity. Qed.
Fact ptand_vp : ptand tv tp = tp. Proof. reflexivity. Qed.
Fact ptand_fv : ptand tf tv = tf. Proof. reflexivity. Qed.
Fact ptand_ff : ptand tf tf = tf. Proof. reflexivity. Qed.
Fact ptand_fp : ptand tf tp = tf. Proof. reflexivity. Qed.
Fact ptand_pv : ptand tp tv = tp. Proof. reflexivity. Qed.
Fact ptand_pf : ptand tp tf = tf. Proof. reflexivity. Qed.
Fact ptand_pp : ptand tp tp = tp. Proof. reflexivity. Qed.

(* DISJONCTION *)
Definition ptor : ptbool -> ptbool -> ptbool := fun a b => fun T => fun x y z => a T x (b T x y z) (b T x z z).

Fact ptor_vv : ptor tv tv = tv. Proof. reflexivity. Qed.
Fact ptor_vf : ptor tv tf = tv. Proof. reflexivity. Qed.
Fact ptor_vp : ptor tv tp = tv. Proof. reflexivity. Qed.
Fact ptor_fv : ptor tf tv = tv. Proof. reflexivity. Qed.
Fact ptor_ff : ptor tf tf = tf. Proof. reflexivity. Qed.
Fact ptor_fp : ptor tf tp = tp. Proof. reflexivity. Qed.
Fact ptor_pv : ptor tp tv = tv. Proof. reflexivity. Qed.
Fact ptor_pf : ptor tp tf = tp. Proof. reflexivity. Qed.
Fact ptor_pp : ptor tp tp = tp. Proof. reflexivity. Qed.

(* 2.4 Produits et sommes avec typage polymorphe *)
(* 2.4.1 Produits *)
(* 1. *)
(* type produit d'un nat et d'un bool *)
Definition pprod_nb := forall T:Set, (nat -> bool -> T) -> T.

(* constructeur d’un couple d'un nat et d'un bool *)
Definition ppair_nb: nat -> bool -> pprod_nb :=
  fun a b => fun T => fun k => k a b  .

(* 2. *)
(* type produit d'un nat et d'un bool *)
Definition pprod_bn := forall T:Set, (bool -> nat -> T) -> T.

(* constructeur d’un couple d'un nat et d'un bool *)
Definition ppair_bn: bool -> nat -> pprod_bn :=
  fun a b => fun T => fun k => k a b  .

(* 3. *)
Definition echange_nb_bn: pprod_nb -> pprod_bn := fun nb => ppair_bn (nb bool (fun a b => b)) (nb nat (fun a b => a)).

(* exemples *)
Compute ppair_nb 5 true.
Compute echange_nb_bn (ppair_nb 5 true).

(* preuve *)
Fact p_echange_nb_bn: forall a:nat, forall b:bool, echange_nb_bn (ppair_nb a b) = ppair_bn b a.
Proof.
  reflexivity.
Qed.

(* 4. *)
Definition pprod : Set -> Set -> Set := fun U V => forall T:Set, (U -> V -> T) -> T.
Definition ppair : forall A B:Set, A -> B -> pprod A B := fun A B:Set => fun (a:A) (b:B) => fun T:Set => fun k:(A -> B -> T) => k a b.

Compute ppair nat bool 5 true.
Compute ppair nat nat 5 7.
Compute ppair bool nat false 2.
Compute ppair bool bool true false.

(* 5. *)
Definition pprod_nb2 := pprod nat bool.
Definition ppair_nb2 := ppair nat bool.  
Fact pprod_nb_pprod : pprod_nb2 = pprod_nb. Proof. reflexivity. Qed.

Definition pprod_bn2 := pprod bool nat.
Definition ppair_bn2 := ppair bool nat. 
Fact pprod_bn_pprod : pprod_bn2 = pprod_bn. Proof. reflexivity. Qed.

(* 6. *)
Compute ppair nat bool 5 true.
Compute ppair nat bool 7 false.
Compute ppair bool nat true 5.
Compute ppair bool nat false 7.

(* 7. *)
Definition echange : forall A B:Set, pprod A B -> pprod B A := fun A B => fun c => ppair B A (c B (fun a b =>  b)) (c A (fun a b => a)).

(* 8. *)
Lemma p_echange : forall A B:Set, forall (a:A) (b:B), forall c:pprod A B, c = ppair A B a b -> c = echange B A (echange A B c).
Proof.
  intros.
  replace c.
  cbv delta [echange].
  cbv delta [ppair].
  cbv beta.
  reflexivity.
Qed.

(* 2.4.2 Sommes *)
(* 1. *)
Definition psom (U V : Set) : Set := forall T:Set, (U -> T) -> (V -> T) -> T.
Definition C1 (U V: Set) : U -> psom U V := fun u => fun T:Set => fun k1:U->T => fun k2:V->T => k1 u.
Definition C2 (U V: Set) : V -> psom U V := fun v => fun T:Set => fun k1:U->T => fun k2:V->T => k2 v.

Compute C1 nat bool 5.
Compute C2 nat bool true.

Variable t1:psom nat bool .

Compute t1 nat (fun a =>1) (fun b => 2).

(* 2. *)
(* Section 2 TD 4 *)
Section S2TD4.
  (* 1. *)
  Definition f1 : psom nat bool -> nat := fun c => c nat (fun a => 2*a) (fun b => match b with true => 1 | false => 0 end).
  Compute f1 (C1 nat bool 5).
  Compute f1 (C2 nat bool true).
  Compute f1 (C2 nat bool false).

  (* 2. 3. 4.*)
  (* On utilise ici les types polymorphes, on n'a donc plus besoin de définir des types destinés à renvoyer un unique type*)
  Definition f3 : psom nat bool -> pprod bool nat:= fun c => c (pprod bool nat) (fun n => ppair bool nat true n) (fun b => match b with
                                                                                                            |true => ppair bool nat false 1
                                                                                                            |false => ppair bool nat false 0 end).
  Compute f3 (C1 nat bool 5).
  Compute f3 (C2 nat bool true).
  Compute f3 (C2 nat bool false).
  
End S2TD4.

(* 2.5 Entier de Church avec typage polymorphe *)
(* 1. (Section 2 du TD3) *)
Definition pnat := forall T:Set, (T -> T) -> (T -> T).
Definition pO:pnat  := fun T:Set => fun (f:T->T) (x:T) => x.
Definition pS:pnat->pnat := fun n:pnat => fun T => fun (f:T->T) (x:T) => f (n T f x).

Compute pO.
Compute pS pO.

Definition padd:pnat->pnat->pnat := fun n m :pnat => fun T:Set => fun f x => n T f (m T f x).

Compute padd (pS pO) (pS (pS pO)). (* 1 + 2 = 3 *)
Compute padd pO pO. (* 0 + 0 = 0 *)

Lemma padd_associativite : forall a b c :pnat, padd (padd a b) c = padd a (padd b c).
Proof.
  intros.
  cbv delta [padd].
  cbv beta.
  reflexivity.
Qed.

Definition pmul:pnat->pnat->pnat := fun n m :pnat => fun T:Set => fun f =>  n T (m T f).

Compute pmul (pS (pS pO)) (pS (pS (pS pO))). (* 2 * 3 = 6 *)

Definition ptz:pnat->pbool := fun n:pnat => fun T:Set =>  fun x y =>  n T (fun z => y) x.

Compute ptz pO.
Compute ptz (pS pO).

(* Preuve que ptz renvoie ptr pour l'entier de Church 0. *)
Lemma p_ptz_ptr : (forall c:pnat, c=pO -> ptz c = ptr).
Proof.
  intros.
  cbv delta [ptr].
  cbv delta [ptz].
  cbv beta.
  replace c.
  cbv delta [pO].
  cbv beta.
  reflexivity.
Qed.

(* Preuve que ptz renvoie pfa pour tout entier de Church différent de 0 en utilisant un type inductif. *)
Inductive pnat_num :Set :=
|O :pnat_num
|S :pnat_num -> pnat_num.

Fixpoint pnat_of n :=
  match n with
    | O => pO
    | S n => pS (pnat_of n)
  end.

Lemma p_ptz_pfa : (forall c:pnat_num, pnat_of(c)<>pO -> ptz (pnat_of c) = pfa).
Proof.
  intros.
  induction c ; tauto.
Qed.

(* 2. *)

