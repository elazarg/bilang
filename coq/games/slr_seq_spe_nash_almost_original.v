(*******************************************)
(*                                         *)
(*          slr_seq_spe_nash.v             *)
(*                                         *)
(*           St\u00c3\u00a9phane Le Roux              *)
(*                                         *)
(*     LIP (ENS Lyon, CNRS, INRIA)         *)
(*                                         *)
(*             Coq v8.1                    *)
(*                                         *)
(*              2007/04                    *)
(*                                         *)
(*******************************************)


Require Import List.
Require Import Relations.
Require Import Peano_dec.
Require Import omega.Omega.
 
Set Implicit Arguments.  

(* ============== *) 
(* === Preliminaries === *) 
(* ============== *)

Section Preliminaries.

Variable A : Set.

Lemma map_inverse : forall (B : Set)(f : A -> B) g,
(forall x, g (f x)=x) -> forall l, map g (map f l)=l.

Proof.
induction l; simpl; intros. trivial. rewrite (H a). rewrite IHl. trivial. 
Qed.

Lemma map_app : forall (B : Set)l l' (f : A -> B), map f (l++l') = (map f l)++(map f l').

Proof.
induction l; simpl; trivial. intros. rewrite (IHl l'). trivial.    
Qed.

Definition restriction {T: Type} R l (x y: T) : Prop := In x l /\ In y l /\ R x y.
Definition is_restricted {T: Type} R l : Prop := forall (x y: T), R x y -> In x l /\ In y l.

Definition sub_rel {T: Type} (R R': T -> T -> Prop) : Prop := forall x y, R x y -> R' x y.

Definition trichotomy {T: Type} R (x y: T) : Prop := R x y \/ x = y \/ R y x.

Definition total {T: Type} (R: relation T) l : Prop := forall x y, In x l -> In y l -> trichotomy R x y.

Lemma sub_rel_restriction_incl : forall (B : Set)(l l' : list B) R, 
incl l l' -> (forall x y, (restriction R l x y) -> (restriction R l' x y)).

Proof.
unfold incl, sub_rel, restriction. intros. split. apply H. tauto. split. apply H. tauto. tauto. 
Qed.
(*
Lemma restricted_clos_trans {T: Type} : forall (R: relation T) (l: list T),
  is_restricted R l -> is_restricted (clos_trans T R) l.
*)

Fixpoint is_path {T: Type} (R: relation T) x y l {struct l} : Prop :=
match l with
| nil => R x y
| z::l' => R x z /\ is_path R z y l'
end.

Lemma clos_trans_path : forall {T: Type} {R: relation T} x y,
  clos_trans T R x y -> exists l, is_path R x y l.
Proof.
  intros.
  induction H.
  + exists nil; assumption.
  + inversion_clear IHclos_trans1 as [l1 Pxy].
    inversion_clear IHclos_trans2 as [l2 Pyz].
    pose (t_trans T R x y z H H0).
    exists (l1 ++ l2).
Admitted.


Definition eq_dec := forall (x y: A), {x=y}+{x<>y}.

Inductive try_add_arc (R: A -> A -> Prop) x y : A -> A -> Prop :=
| keep : forall z t, R z t -> try_add_arc R x y z t
| try_add : x<>y -> ~ R y x -> try_add_arc R x y x y
.

Fixpoint try_add_arc_one_to_many (R: A -> A -> Prop) x l {struct l} : A -> A -> Prop :=
match l with
| nil => R
| y::l' => clos_trans _ (try_add_arc (try_add_arc_one_to_many R x l') x y)
end.

Fixpoint try_add_arc_many_to_many (R: relation A) l' l {struct l'}: relation A :=
match l' with
| nil => R
| x::l'' => try_add_arc_one_to_many (try_add_arc_many_to_many R l'' l) x l
end.

Definition LETS (R: A -> A -> Prop) l :=
  try_add_arc_many_to_many (clos_trans _ (restriction R l)) l l.

Definition rel_dec (P: A -> A -> Prop) := (forall x y, {P x y}+{~P x y}).
Definition irreflexive (R: A -> A -> Prop) : Prop := forall x, ~ R x x.

Definition eq_midex := forall (x y: A), x=y \/ x<>y.
Axiom LETS_sub_rel : forall (R: relation A) l, sub_rel (clos_trans _ (restriction R l)) (LETS R l).
Axiom LETS_dec : eq_dec -> forall R, rel_dec R -> forall l, rel_dec (LETS R l).
Axiom LETS_restricted : forall (R: relation A) l, is_restricted (LETS R l) l.
Axiom LETS_irrefl : eq_midex -> forall (R: relation A) l,
  (irreflexive (clos_trans _ (restriction R l)) <-> irreflexive (LETS R l)).
Axiom LETS_transitive : forall (R: relation A) l, transitive _ (LETS R l).


Section listforall.

Variable Q : A -> Prop.

Fixpoint listforall (l : list A) : Prop :=
match l with
| nil => True
| x::l' => Q x /\ listforall l'
end.

Lemma listforall_app :  forall l' l, listforall l -> listforall l' -> listforall (l++l'). 

Proof.
induction l; simpl; intros; tauto.
Qed.

Lemma listforall_appl :  forall l' l, listforall (l++l') -> listforall l. 

Proof.
induction l; simpl; intros; tauto. 
Qed. 
 
Lemma listforall_appr :  forall l' l, listforall (l++l') -> listforall l'. 

Proof.
induction l; simpl; intros; tauto. 
Qed. 

Lemma listforall_In : forall x l, In x l -> listforall l -> Q x. 

Proof.
induction l; simpl; intros. tauto. destruct H. rewrite H in H0. tauto. tauto.
Qed.

End listforall.


Variable P : A -> A -> Prop.

Fixpoint rel_vector (l l' : list A) {struct l}: Prop :=
match l with
| nil => l'=nil
| x::l2 => match l' with
               | nil => False
               | x'::l2' => P x x' /\ rel_vector l2 l2'
               end
end.

Lemma rel_vector_app_cons_same_length : forall a a' m m' l l', 
rel_vector (l++a::m) (l'++a'::m') -> length l=length l' -> P a a'. 

Proof. 
induction l; simpl; intros; destruct l'; simpl in H; simpl in H0. tauto. pose  (O_S (length l') H0). 
contradiction. pose  (O_S (length l) (sym_equal H0)). contradiction. 
apply IHl with l'. tauto. omega. 
Qed.

Lemma rel_vector_app_cons_exists : forall a q l m, 
rel_vector l (m++a::q) -> {x : A | In x l /\ P x a}.

Proof.
induction l; simpl; intros. destruct m; simpl in H; inversion H. 
destruct m; simpl in H. exists a0. tauto. destruct (IHl m). tauto. 
exists x. tauto. 
Qed.

Lemma rel_vector_app_cons_different_length : forall l a m l' a' m',
rel_vector (l++a::m) (l'++a'::m') -> length l<>length l' ->  {x : A | (In x l \/ In x m) /\ P x a'}.

Proof.
induction l; simpl; intros. destruct l'; simpl in H0. tauto. simpl in H. destruct H. 
destruct (rel_vector_app_cons_exists a' m' m l' H1). exists x. tauto. destruct l'; simpl in H. 
exists a. tauto. destruct (IHl a0 m l' a' m'). tauto. simpl in H0. omega. exists x. tauto. 
Qed.

Definition is_no_succ (x : A)(l : list A) := listforall (fun y => ~P x y) l.

Lemma is_no_succ_trans : forall x y l, transitive A P -> P x y -> is_no_succ x l -> is_no_succ y l. 

Proof. 
induction l; simpl; intros. tauto. split. intro. absurd (P x a). tauto. apply H with y; assumption. tauto.
Qed.

Lemma is_no_succ_dec :  rel_dec P -> forall x l, {is_no_succ x l}+{~is_no_succ x l}.

Proof.
unfold rel_dec.
induction l; simpl; intros. tauto. destruct (H x a); tauto. 
Qed.

(* Choice function proved together with its properties, by induction *)
Lemma Choose_and_split : rel_dec P -> forall (l : list A)(x : A), 
{triple : list A * A * list A | let (double,right):=triple in let (left,choice):=double in
 x::l=(left++(choice::right)) /\ is_no_succ choice right /\ 
 (forall left' choice' right', left=left'++(choice'::right') ->
 ~is_no_succ choice' (right'++(choice::right))) /\
(irreflexive P -> transitive A P -> is_no_succ choice left)}.  

Proof.

unfold rel_dec.
induction l; intros. 
(* nil case *)
exists ((nil : list A, x), (nil : list A)). simpl. repeat (split; trivial). 
intros. destruct (app_eq_nil left' (choice'::right')(sym_equal H0)). inversion H2. 
(* cons case *)
destruct (is_no_succ_dec H x (a::l)).
(**)
exists ((nil : list A,x),a::l). repeat (split; trivial).  
intros. destruct (app_eq_nil left' (choice'::right')(sym_equal H0)). inversion H2. 
(**) 
destruct (IHl a). destruct x0. destruct p. decompose [and] y. clear y. 
exists ((x::l1,a0),l0). split. rewrite H0. rewrite (app_comm_cons l1 (a0::l0) x). trivial. 
split. assumption. split. intros. destruct left'. simpl in H3. inversion H3. 
rewrite <- H6. rewrite <- H7. rewrite <- H0. assumption. 
rewrite <- (app_comm_cons left' (choice'::right') a1) in H3. inversion H3. apply H1 with left'. 
assumption. intros. simpl. split. intro. absurd (is_no_succ x (a::l)). assumption. 
rewrite H0. apply is_no_succ_trans with a0. assumption. assumption. unfold is_no_succ. 
apply listforall_app. tauto. split. apply H3. assumption. tauto.
Qed. 

End Preliminaries.


(* ============== *) 
(* === Game Theory === *) 
(* ============== *) 
 
(*  Outcome is a set of "end-of-the-game situations" *) 
Variable Outcome : Set.
(* Agent is some set of "players" *)  
Variable Agent : Set.
 
(* ============= *) 
(* === Games === *) 
(* ============= *) 
 
(* A game *) 
Inductive Game : Set := 
  | gL : Outcome -> Game 
  | gN : Agent -> Game -> list Game -> Game.


(* Define an induction principle for Game *)
Section correct_Game_ind.

Variables
(P : Game -> Prop)
(Q : Game -> list Game -> Prop).

Hypotheses
(H : forall oc, P (gL oc))
(H0 : forall g, P g -> Q g nil)
(H1 : forall g , P g -> forall g' l, Q g' l -> Q g' (g::l))
(H2 : forall g l, Q g l -> forall a, P (gN a g l)).

Fixpoint Game_ind2 (g : Game) : P g :=
match g as x return P x  with
| gL oc => H oc
| gN a g' l => H2 
                           ((fix G_ind2 (l' : list Game){struct l'} : Q g' l' :=
                           match l' as x return Q g' x with
                           | nil => H0 (Game_ind2 g')
                           | g3::l'' => H1 (Game_ind2 g3) (G_ind2 l'')
                           end )
                            l) a
end.

End correct_Game_ind.

(* The outcomes used to build a game *)
Fixpoint UsedOutcomes (g : Game) : list Outcome := 
match g with 
| gL oc => oc::nil 
| gN _ g' l =>  ((fix ListUsedOutcomes  (l' : list Game) : list Outcome :=
                         match l' with
                         | nil => nil
                         | x::m => (UsedOutcomes x)++(ListUsedOutcomes m) 
                         end) (g'::l))
end.

Lemma UsedOutcomes_gN : forall a g g' l,
In g (g'::l) -> incl (UsedOutcomes g) (UsedOutcomes (gN a g' l)).

Proof.
induction l; simpl; intros. destruct H. rewrite H. rewrite <- (app_nil_end (UsedOutcomes g)). 
apply incl_refl. contradiction. assert (a0=g \/ g'=g \/ In g l). tauto. 
destruct H0. rewrite H0. apply incl_appr. apply incl_appl. apply incl_refl. unfold incl in *|-* . 
intros. simpl in IHl. destruct (in_app_or  (UsedOutcomes g') 
((fix f (l' : list Game) : list Outcome := match l' with | nil => nil (A:=Outcome) | x :: m =>
UsedOutcomes x ++ f m end) l) a1). apply IHl. assumption. assumption. 
apply in_or_app. tauto. apply in_or_app. constructor 2. apply  in_or_app. tauto. 
Qed.

Lemma UsedOutcomes_gN_listforall : forall a g loc l,
incl (UsedOutcomes (gN a g l)) loc -> listforall (fun g' : Game => incl (UsedOutcomes g') loc) (g::l).

Proof.
unfold incl. split. intros. apply H. simpl. apply in_or_app. tauto. induction l; simpl; intros. trivial. 
split. intros. apply H. simpl. apply in_or_app. constructor 2. apply in_or_app. tauto. apply IHl. 
intros. apply H. simpl in H0. destruct ((in_app_or (UsedOutcomes g)  
((fix f (l' : list Game) : list Outcome := match l' with | nil => nil (A:=Outcome) |
 x :: m => UsedOutcomes x ++ f m end) l)) a1). assumption. simpl. apply in_or_app. tauto. 
simpl. apply in_or_app. constructor 2. apply in_or_app. tauto. 
Qed. 


(* ============ *) 
(* === Strategies === *) 
(* ============ *) 
 
(* A strategy *) 
Inductive Strat : Set := 
  | sL : Outcome -> Strat 
  | sN : Agent -> list Strat -> Strat -> list Strat -> Strat.


(* Define an induction principle for Strat *)
Section correct_Strat_ind.

Variables
(P : Strat -> Prop)
(Q : list Strat -> Strat -> list Strat -> Prop).

Hypotheses
(H : forall oc, P (sL oc))
(H0 : forall sc, P sc -> Q nil sc nil)
(H1nil : forall s , P s -> forall sc sr, Q nil sc sr -> Q nil sc (s::sr))
(H1 : forall s , P s -> forall sc sl sr, Q sl sc sr -> Q (s::sl) sc sr)
(H2 : forall sc sl sr, Q sl sc sr -> forall a, P (sN a sl sc sr)).

Fixpoint Strat_ind2 (s : Strat) : P s :=
match s as x return P x  with
| sL oc => H oc
| sN a sl sc sr => H2 
                           ((fix S_ind2 (sl' : list Strat){struct sl'} : Q sl' sc sr :=
                           match sl' as x return Q x sc sr with
                           | nil =>  (fix Snil_ind2 (sr' : list Strat) : Q nil sc sr' :=
                                         match sr' as x return Q nil sc x with
                                         | nil => H0 (Strat_ind2 sc)
                                         | s'::sr'' => H1nil (Strat_ind2 s')(Snil_ind2 sr'')
                                         end) sr
                           | s'::sl'' => H1 (Strat_ind2 s') (S_ind2 sl'')
                           end ) sl) a
end.

End correct_Strat_ind.

(* The game corresponding to a strategy *) 
Fixpoint s2g (s : Strat) : Game := 
match s with 
| sL oc => gL oc 
| sN a sl sc sr =>  match sl with
                             | nil => gN a (s2g sc) (map s2g sr)
                             | s'::sl' => gN a (s2g s') ((map s2g sl')++(s2g sc)::(map s2g sr))
                             end
end.


Lemma map_s2g_sN_s2g : forall a sl sc sr sl' sc' sr',
map s2g (sl ++ sc :: sr) = map s2g (sl' ++ sc' :: sr') ->
s2g (sN a sl sc sr) = s2g (sN a sl' sc' sr').

Proof.
intros. destruct sl; destruct sl'; simpl in H|-* ; inversion H. trivial. 
rewrite H2. rewrite (map_app sl' (sc'::sr') s2g). trivial. 
rewrite (map_app sl (sc::sr) s2g). trivial. 
rewrite (map_app sl (sc::sr) s2g) in H2. rewrite (map_app sl' (sc'::sr') s2g) in H2.
simpl in H2. rewrite H2. trivial. 
Qed.

(* The outcome of a strategy for a specific agent *) 
Fixpoint InducedOutcome (s : Strat) : Outcome := 
match s with 
| sL oc => oc 
| sN a sl sc sr => InducedOutcome sc 
end. 

Lemma UsedOutcomes_sN_incl : forall a sl sc sr, 
incl (UsedOutcomes (s2g sc)) (UsedOutcomes (s2g (sN a sl sc sr))).

Proof.
induction sl; intros. simpl. apply incl_appl. apply incl_refl. 
destruct sl; simpl in *|-* ; apply incl_appr; apply IHsl.   
Qed.

Lemma Used_Induced_Outcomes : forall s : Strat,
In (InducedOutcome s) (UsedOutcomes (s2g s)). 

Proof.
intro. assert (let P:=fun s => In (InducedOutcome s) (UsedOutcomes (s2g s)) in P s). 
apply Strat_ind2 with
(fun (l : list Strat) s (l' : list Strat) => In (InducedOutcome s) (UsedOutcomes (s2g s))); 
try (simpl;  tauto). 
intros. apply UsedOutcomes_sN_incl. assumption. simpl in H. assumption.  
Qed. 

Lemma map_s2g_gL_InducedOutcome : forall ls loc,
map s2g ls =map (fun y => gL y) loc -> map InducedOutcome ls = loc.

Proof.
induction ls; simpl; intros; destruct loc. trivial. inversion H. inversion H. inversion H. 
rewrite (IHls loc). destruct a. inversion H1. trivial. destruct l; inversion H1. assumption.  
Qed.

(* Agent Convertibility between strategies *)   
Inductive Conv : Agent -> Strat -> Strat -> Prop :=
| convLeaf : forall a0 oc, Conv a0 (sL oc)(sL oc)
| convNode : forall a0 a sl sl' sc sc' sr sr',  (length sl=length sl' \/ a = a0) ->
ListConv a0 (sl++(sc::sr)) (sl'++(sc'::sr')) ->
Conv a0 (sN a sl sc sr)(sN a sl' sc' sr')
with
ListConv : Agent -> list Strat -> list Strat -> Prop :=
| lconvnil : forall a0, ListConv a0 nil nil
| lconvcons : forall a0 s s' tl tl', Conv a0 s s' -> ListConv a0 tl tl' ->
ListConv a0 (s::tl)(s'::tl').

Scheme conv_lconv_ind := Minimality for Conv Sort Prop
with lconv_conv_ind := Minimality for ListConv Sort Prop.

(* Relation between Conv, ListConv, and rel_vector *)
Lemma ListConv_rel_vector : forall a l l',
ListConv a l l' -> rel_vector (Conv a) l l'.

Proof.
induction l; intros. inversion H. simpl. trivial. destruct l'; simpl. inversion H. 
inversion H. split. assumption. apply IHl. assumption. 
Qed.

Lemma rel_vector_ListConv : forall a l l',
rel_vector (Conv a) l l' -> ListConv a l l' .

Proof.
induction l; intros. inversion H. constructor. destruct l'. inversion H. simpl in H. 
constructor. tauto. apply IHl. tauto. 
Qed.

Lemma  Conv_refl : forall a s , Conv a s s.

Proof.
intros. assert (let P:= fun s => Conv a s s in P s). 
apply Strat_ind2 with  (fun sl sc sr => ListConv a (sl++(sc::sr)) (sl++(sc::sr))); simpl; intros.
constructor. 
constructor 2. assumption. constructor.
inversion H0. 
constructor. assumption. constructor. assumption. assumption. 
constructor. assumption. assumption. constructor 2. tauto. assumption. 
simpl in H. assumption. 
Qed. 

Lemma ListConv_refl : forall a l, ListConv a l l.

Proof.
intros. apply rel_vector_ListConv. induction l; simpl. trivial. pose (Conv_refl a a0). tauto.
Qed.

(* Agent conversion preserves the underlying game *) 
Lemma Conv_s2g : forall (a : Agent)(s s' : Strat), Conv a s s' -> s2g s = s2g s'. 

Proof.
intros. assert (let P:= (fun a s s' => s2g s = s2g s') in P a s s').
apply conv_lconv_ind with (fun a0 l l' => ListConv a0 l l' -> map s2g l=map s2g l'); intros. 
trivial. apply map_s2g_sN_s2g. tauto. trivial. simpl. rewrite H1. rewrite H3. trivial. assumption. 
assumption. simpl in H0. assumption. 
Qed.   

(* ============ *) 
(* === Equilibria === *) 
(* ============ *) 
 
Section NE_SPE.

(* Preference *) 
Variable OcPref : Agent -> relation Outcome. 
 
Definition StratPref (a : Agent)(s s' : Strat) : Prop := 
 OcPref a (InducedOutcome s)(InducedOutcome s').
 
(* Definition of happiness *)
Definition Happy (s : Strat)(a : Agent) : Prop := 
  forall s', Conv a s s' -> ~StratPref a s s'.
 
(* Definition of Nash equilibrium *) 
Definition Eq (s : Strat) : Prop := forall a, Happy s a. 

(* Subgame perfect equilibrium *) 
Fixpoint SPE (s : Strat) : Prop := Eq s /\ 
match s with 
| sL oc =>  True 
| sN a sl sc sr => (listforall SPE sl) /\ SPE sc /\ (listforall SPE sr) 
end.

(* Subgame perfect equilibrium is equilibrium *) 
Lemma SPE_is_Eq : forall s : Strat, SPE s -> Eq s. 

Proof.
intros. destruct s; simpl in H; tauto. 
Qed. 

Lemma Eq_subEq_choice : forall a sl sc sr,
(forall s s', In s sl \/ In s sr -> Conv a s s' -> ~StratPref a sc s') ->
Eq sc -> Eq (sN a sl sc sr).

Proof.
unfold Eq, Happy. intros. intro. destruct s'; inversion H1.  
unfold StratPref in H2. simpl in H2. 
destruct (eq_nat_dec (length sl) (length l)). absurd (StratPref a0 sc s').
apply H0. apply  rel_vector_app_cons_same_length with Strat sr l0 sl l. 
apply ListConv_rel_vector. assumption. assumption. unfold StratPref. assumption. 
assert (a1=a0). tauto. 
destruct (rel_vector_app_cons_different_length (Conv a0) sl sc sr l s' l0). 
apply ListConv_rel_vector. assumption. assumption. rewrite H9 in H. rewrite H14 in H. 
absurd (StratPref a0 sc s'). apply H with x; tauto . unfold StratPref. assumption. 
Qed. 


Section BI. 

Hypothesis OcPref_dec : forall (a : Agent), rel_dec (OcPref a). 

Lemma StratPref_dec : forall (a : Agent), rel_dec (StratPref a).

Proof.
unfold StratPref. do 3 intro. apply OcPref_dec.
Qed.
 

(* Definition of fast backward induction *)
Fixpoint BI (g : Game) : Strat := 
match g with 
| gL oc => sL oc 
| gN a g l => let (triple,_):=Choose_and_split (StratPref_dec a) (map BI l) (BI g) in
                      let (double,sr):= triple in
                      let (sl,sc):= double in
                      sN a sl sc sr
end.

Lemma BI_s2g : forall g : Game, s2g (BI g)=g. 

Proof.
intro. assert (let P:= fun g => s2g (BI g) = g in P g). 
apply Game_ind2 with (fun g l => s2g (BI g) = g /\ map s2g (map BI l)=l); simpl; intros.  
trivial. tauto. rewrite H. rewrite (proj2 H0). tauto. 
destruct (Choose_and_split  (StratPref_dec a) (map BI l) (BI g0)).
destruct x. destruct p. decompose [and] y. clear y. destruct l1; simpl in H0|-* . inversion H0. 
rewrite (proj1 H). rewrite (proj2 H). trivial. inversion H0. rewrite (proj1 H). rewrite <- (proj2 H). 
rewrite H6. rewrite  (map_app l1 (s::l0) s2g). simpl. trivial. simpl in H. assumption. 
Qed.

Hypothesis OcPref_irrefl : forall (a : Agent), irreflexive (OcPref a). 

Hypothesis OcPref_trans : forall (a : Agent), transitive Outcome (OcPref a).

Lemma StratPref_irrefl : forall (a : Agent), irreflexive (StratPref a).

Proof.
unfold StratPref. do 2 intro. apply OcPref_irrefl. 
Qed. 

Lemma StratPref_trans : forall (a : Agent), transitive Strat (StratPref a).

Proof.
repeat intro. unfold transitive in *|- . unfold StratPref in *|-* . 
apply OcPref_trans with (InducedOutcome y); assumption. 
Qed.

Lemma Leaf_Eq : forall oc : Outcome, Eq (sL oc). 

Proof.
do 4 intro. destruct s'. inversion H. apply StratPref_irrefl. inversion H. 
Qed.

Lemma BI_SPE :  forall loc, (forall (a : Agent), total (OcPref a) loc) ->
forall g : Game, incl (UsedOutcomes g) loc -> SPE (BI g).

Proof.
intros loc H.
(* Slightly Change the Form of the Goal *)
cut (let P:= fun g => incl (UsedOutcomes g) loc -> SPE (BI g) in forall g, P g). tauto.

(* By Induction on Games *)
apply Game_ind2 with
  (fun g l => listforall (fun g' => incl (UsedOutcomes g') loc) (g::l) ->
              SPE (BI g) /\ listforall SPE (map BI l)); simpl.
(* Three First Cases *)
- intuition. apply Leaf_Eq.
- tauto.
- tauto.
(* Last Case *)
-
  (* Explicit BI Choice *) 
  intros.
  destruct (Choose_and_split (StratPref_dec a) (map BI l) (BI g)).
  destruct x.
  destruct p.
  decompose [and] y. clear y.
  (* Prove Sub-SPE *)
  assert (listforall SPE (l1 ++ s :: l0)). {
    rewrite <- H2. apply H0.
    apply UsedOutcomes_gN_listforall with a.
    assumption.
  }
  pose (listforall_appr SPE (s::l0) l1 H5).
  pose (listforall_appl SPE (s::l0) l1 H5).
  (** Eq, Using Lemma  Eq_subEq_choice **)
  split; auto.
  apply Eq_subEq_choice. 
  (* First Condition to Verify *)
  ++ do 4 intro.
    (* Prove Sub-Eq *)
    assert (Eq s0). {
      apply SPE_is_Eq.
      apply listforall_In with Strat (l1++(s::l0)); try assumption.
      apply in_or_app. simpl. tauto.
    }
    (* Recall Two Maximalities *) 
    assert (~StratPref a s0 s') by (apply H9; assumption).
    assert (~StratPref a s s0). {
      assert (let Q:= fun x => ~ StratPref a s x in Q s0). {
        destruct H7.
        -- apply listforall_In with Strat l1.
           --- assumption.
           --- apply H6. apply StratPref_irrefl. apply StratPref_trans.
        -- apply listforall_In with Strat l0.
           --- assumption.
           --- exact H4.
      }
      assumption.
    }
    (* An Outcome-List Inclusion*)
    assert (incl (UsedOutcomes(s2g s0)) loc). {
      do 2 intro. apply H1. pose UsedOutcomes_gN.
      unfold incl in i.
      apply i with (s2g s0); auto.
      rewrite <- (map_inverse BI s2g BI_s2g (g :: l)).
      apply in_map.
      cutrewrite (map BI (g :: l)=l1 ++ s :: l0).
      ** apply in_or_app. simpl. tauto.
      ** simpl. assumption.
    }
    (* Justify and Perform a Case Splitting on  StratPref *)
    unfold StratPref in *.
    destruct (H a (InducedOutcome s0)(InducedOutcome s')).
    * apply H12. apply Used_Induced_Outcomes.
    * apply H12. rewrite (Conv_s2g H8). apply Used_Induced_Outcomes.
    * contradiction.
    *
      destruct H13 as [ <- | ]; try assumption.
      intro.
      apply (H11 (OcPref_trans H14 H13)).
    (**)
  ++ apply SPE_is_Eq. simpl in l2. tauto.
Qed.

End BI.

End NE_SPE.

Lemma Eq_order_inclusion :  forall OcPref OcPref' s, 
(forall a : Agent, sub_rel (restriction (OcPref a) (UsedOutcomes (s2g s))) (OcPref' a)) -> Eq OcPref' s -> Eq OcPref s.

Proof. 
unfold sub_rel, Eq, Happy, StratPref, restriction. intros. intro. 
absurd (OcPref' a (InducedOutcome s) (InducedOutcome s')). apply H0. assumption. 
apply H. split. apply  Used_Induced_Outcomes. split. rewrite (Conv_s2g H1). 
apply  Used_Induced_Outcomes. assumption. 
Qed.
(*
Axiom transitive_sub_rel: forall {T: Type} (R R': relation T), sub_rel R R' ->
  (forall x y z, clos_trans T R x y -> R' x y -> clos_trans T R y z -> R' y z -> R' x z)
  -> sub_rel (clos_trans T R) R'.
*)

 Axiom SPE_order_inclusion : forall OcPref OcPref' s, 
(forall a : Agent, sub_rel (restriction (OcPref a) (UsedOutcomes (s2g s))) (OcPref' a)) -> SPE OcPref' s -> SPE OcPref s. 

(* ================================ *) 
(* === Equivalence Between Acyclicity, SPE, and Eq  === *) 
(* ================================ *) 

(* Equality is decidable on outcomes*)
Hypothesis Outcome_dec : eq_dec Outcome.

Axiom acyclic_SPE : forall OcPref,
(forall a, rel_dec (OcPref a)) ->
(forall a, irreflexive (clos_trans Outcome (OcPref a))) -> 
  forall g, {s : Strat | s2g s=g /\ SPE OcPref s}. 

Lemma SPE_Eq : forall OcPref,
(forall a, rel_dec (OcPref a)) ->
(forall g : Game, {s : Strat | s2g s=g /\ SPE OcPref s}) -> 
forall g : Game, {s : Strat | s2g s=g /\ Eq OcPref s}.  

Proof.
intros ? H H0 ?. destruct (H0 g). exists x. split. tauto. apply SPE_is_Eq. tauto. 
Qed. 

Axiom Eq_acyclic : forall OcPref,
(forall a, rel_dec (OcPref a)) ->
(forall g : Game, {s : Strat | s2g s=g /\ Eq OcPref s}) -> 
forall a : Agent, irreflexive (clos_trans Outcome (OcPref a)). 
