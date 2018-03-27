(*******************************************)
(*                                         *)
(*          slr_seq_spe_nash.v             *)
(*                                         *)
(*           St\u00e9phane Le Roux              *)
(*                                         *)
(*     LIP (ENS Lyon, CNRS, INRIA)         *)
(*                                         *)
(*             Coq v8.1                    *)
(*                                         *)
(*              2007/04                    *)
(*                                         *)
(*******************************************)


Require Import List.
(* Require Import slr_topo_sorting. *)
Require Import Relations.
Require Import Peano_dec.

Require Import omega.Omega.
Require Import Relations.

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

Variable Q : A -> Prop.

Definition listforall := Forall.
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

Definition is_no_succ (x : A)(l : list A) := Forall (fun y => ~P x y) l.

Lemma is_no_succ_trans : forall x y l, transitive _ P -> P x y -> is_no_succ x l -> is_no_succ y l. 

Proof.
unfold is_no_succ.
induction l; simpl; intros.
+ auto.
+ inversion H1 as [U | a0].
  apply Forall_cons; intuition.
  apply H2.
  apply (H _ _ _ H0 H6).
Qed.

Definition rel_dec {T: Type} (P: T -> T -> Prop) := (forall x y, {P x y}+{~P x y}).

Lemma is_no_succ_dec :  rel_dec P -> forall x l, {is_no_succ x l}+{~is_no_succ x l}.

Proof.
unfold is_no_succ. intros H x l.
induction l; simpl; intros. left. apply Forall_nil.
destruct (H x a).
+ right. intro. inversion H0. auto.
+ inversion IHl; auto.
  right. intro. inversion H1. auto.
Qed.

Definition irreflexive {T: Type} (R: T -> T -> Prop) : Prop := forall x, ~ R x x.

(* Choice function proved together with its properties, by induction *)
Lemma Choose_and_split : rel_dec P -> forall (l : list A)(x : A),
{triple : list A * A * list A | let (double,right):=triple in let (left,choice):=double in
 x::l=(left++(choice::right)) /\ is_no_succ choice right /\
 (forall left' choice' right', left=left'++(choice'::right') ->
 ~is_no_succ choice' (right'++(choice::right))) /\
(irreflexive P -> transitive A P -> is_no_succ choice left)}.

Proof.
unfold is_no_succ.
intro H.
induction l.
(* nil case *)
+ intro x.
exists ((nil : list A, x), (nil : list A)).
 simpl. repeat (split; auto).
intros. destruct (app_eq_nil left' (choice'::right')(sym_equal H0)). inversion H2.
(* cons case *)
+ intro x. destruct (is_no_succ_dec H x (a::l)).
(**)
* exists ((nil : list A,x),a::l). repeat (split; trivial).  
intros. destruct (app_eq_nil left' (choice'::right')(sym_equal H0)). inversion H2.
(**) 
* destruct (IHl a). clear IHl. destruct x0. destruct p. decompose [and] y. clear y.
exists ((x::l1,a0),l0). split.
  - rewrite H0. rewrite (app_comm_cons l1 (a0::l0) x). reflexivity.
-
split.
++ assumption.
++ split.
-- intros. destruct left'.
--- simpl in H3. inversion H3.
rewrite <- H6. rewrite <- H7. rewrite <- H0. assumption.
--- 
rewrite <- (app_comm_cons left' (choice'::right') a1) in H3. inversion H3. apply H1 with left'. assumption.
-- intros.
   apply Forall_cons; auto; intro.
   specialize (H4 H3 H5).
   unfold is_no_succ in n.
   apply n.
   rewrite H0.
destruct l1.
Admitted.
(*
--- simpl in *. inversion H0. subst a0 l. apply Forall_cons. unfold irreflexive in *. intro. apply (H5 _ _ _ H6) in H7. apply (H3 _ H7).
    
    assumption.
   clear n H0 a l H Q H3 H1.
   Search Forall.
   assumption.
--- simpl. split. intro. absurd (is_no_succ x (a::l)). assumption. 
rewrite H0. apply is_no_succ_trans with a0. assumption. assumption. unfold is_no_succ. 
apply listforall_app. tauto. split. apply H3. assumption. tauto.
Qed. 
*)
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
unfold listforall.
unfold incl. intros. apply Forall_cons.
- intros. apply H. simpl. apply in_or_app. tauto.
- induction l; simpl; intros; trivial.
apply Forall_cons. intros. apply H. simpl. apply in_or_app. constructor 2. apply in_or_app. tauto. apply IHl. 
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

Check Strat_ind2.

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
do 2 intro. 
(* Slightly Change the Form of the Goal *)
assert (let P:= fun g => incl (UsedOutcomes g) loc -> SPE (BI g) in forall g, P g). 
(* By Induction on Games *)
apply Game_ind2 with
(fun g l =>  listforall  (fun g' => incl (UsedOutcomes g') loc) (g::l) ->
SPE (BI g) /\ listforall SPE (map BI l)).
(* Three First Cases *)
split. apply Leaf_Eq. trivial. simpl. tauto. simpl. tauto.  
(* Last Case *) 
(* Explicit BI Choice *) 
intros. simpl. destruct  (Choose_and_split (StratPref_dec a) (map BI l) (BI g)). 
destruct x. destruct p. decompose [and] y. clear y. 
(* Prove Sub-SPE *)
assert (listforall SPE (l1 ++ s :: l0)). rewrite <- H2. apply H0. 
apply UsedOutcomes_gN_listforall with a. assumption. 
pose (listforall_appr SPE (s::l0) l1 H5). pose (listforall_appl SPE (s::l0) l1 H5). 
(** Eq, Using Lemma  Eq_subEq_choice **)
split. apply Eq_subEq_choice. 
(* First Condition to Verify *)
do 4 intro.
(* Prove Sub-Eq *)
assert (Eq s0). apply SPE_is_Eq. apply listforall_In with Strat (l1++(s::l0)). apply in_or_app. simpl. 
tauto. assumption. 
(* Recall Two Maximalities *) 
assert (~StratPref a s0 s'). apply H9. assumption. 
assert (~StratPref a s s0). assert (let Q:= fun x => ~ StratPref a s x in Q s0). 
destruct H7. apply listforall_In with Strat l1. assumption. apply H6. apply StratPref_irrefl.
apply StratPref_trans. apply listforall_In with Strat l0. assumption. exact H4. assumption. 
(* An Outcome-List Inclusion*)
assert (incl (UsedOutcomes(s2g s0)) loc). do 2 intro. apply H1. pose UsedOutcomes_gN. 
unfold incl in i. apply i with (s2g s0). rewrite <- (map_inverse BI s2g BI_s2g (g :: l)). 
apply in_map. cutrewrite (map BI (g :: l)=l1 ++ s :: l0). apply in_or_app. simpl. tauto. 
simpl. assumption. assumption. 
(* Justify and Perform a Case Splitting on  StratPref *)
unfold StratPref in *|-* . 
destruct (H a (InducedOutcome s0)(InducedOutcome s')). 
apply H12. apply Used_Induced_Outcomes. apply H12. rewrite (Conv_s2g H8).
apply Used_Induced_Outcomes. contradiction. 
destruct (OcPref_dec a (InducedOutcome s)(InducedOutcome s0)). contradiction. 
(* Continue the Case Splitting *) 
destruct H13. rewrite <- H13. assumption. intro. 
absurd (OcPref a (InducedOutcome s) (InducedOutcome s0)). assumption. 
apply OcPref_trans with (InducedOutcome s'); assumption. 
(**)
apply SPE_is_Eq. simpl in l2. tauto. simpl in l2. tauto. 
(**)
simpl in H0. assumption.  
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

 Lemma SPE_order_inclusion : forall OcPref OcPref' s, 
(forall a : Agent, sub_rel (restriction (OcPref a) (UsedOutcomes (s2g s))) (OcPref' a)) -> SPE OcPref' s -> SPE OcPref s. 

Proof.
do 3 intro. assert (let P:= fun s =>
(forall a : Agent, sub_rel (restriction (OcPref a) (UsedOutcomes (s2g s))) (OcPref' a)) ->
SPE OcPref' s -> SPE OcPref s in P s). apply Strat_ind2 with
(fun sl sc sr =>
(forall a : Agent, sub_rel (restriction (OcPref a) (UsedOutcomes (s2g (sN a sl sc sr)))) (OcPref' a)) ->
listforall (SPE OcPref') sl -> SPE OcPref' sc -> listforall (SPE OcPref') sr ->
listforall (SPE OcPref) sl /\ SPE OcPref sc /\ listforall (SPE OcPref) sr).

simpl. intros. split. apply Eq_order_inclusion with OcPref'; tauto. tauto. 

simpl. intros. rewrite (app_nil_end (UsedOutcomes (s2g sc))) in H.
pose (H H0 H2). tauto. 

intros. assert (SPE OcPref s0). apply H. intro. 
apply transitive_sub_rel with  (restriction (OcPref a) (UsedOutcomes (s2g (sN a nil sc (s0 :: sr))))). 
apply sub_rel_restriction_incl. simpl. apply incl_appr. apply incl_appl. apply incl_refl. apply H1. 
simpl in H4. tauto. assert (True /\ SPE OcPref sc /\ listforall (SPE OcPref) sr). apply H0. intro. 
apply transitive_sub_rel with (restriction (OcPref a) (UsedOutcomes (s2g (sN a nil sc (s0 :: sr))))). 
apply sub_rel_restriction_incl. simpl. apply incl_app. apply incl_appl. apply incl_refl. apply incl_appr. 
apply incl_appr. apply incl_refl. apply H1. trivial. assumption. simpl in H4. tauto. 
simpl. tauto. 

intros. simpl in H2|-* . assert (listforall (SPE OcPref) sl /\ SPE OcPref sc /\ listforall (SPE OcPref) sr). apply H0. intro. 
apply transitive_sub_rel with (restriction (OcPref a) (UsedOutcomes (s2g (sN a (s0 :: sl) sc sr)))). 
apply sub_rel_restriction_incl. simpl. apply incl_appr. destruct sl; simpl; apply incl_refl.  
apply H1. tauto. assumption. assumption. assert (SPE OcPref s0 ). apply H. intro. 
apply transitive_sub_rel with  (restriction (OcPref a) (UsedOutcomes (s2g (sN a (s0 :: sl) sc sr)))). 
simpl. apply sub_rel_restriction_incl. apply incl_appl. apply incl_refl. apply H1. tauto. tauto. 

intros. simpl in H1|-* . split. apply Eq_order_inclusion with OcPref'. assumption. tauto. 
apply H; try tauto. destruct sl; tauto.  

simpl in H. assumption. 
Qed. 
  

(* ================================ *) 
(* === Equivalence Between Acyclicity, SPE, and Eq  === *) 
(* ================================ *) 
 
(* Equality is decidable on outcomes*)
Hypothesis Outcome_dec : eq_dec Outcome.

Theorem acyclic_SPE : forall OcPref,
(forall a, rel_dec (OcPref a)) ->
(forall a, irreflexive (clos_trans Outcome (OcPref a))) -> 
  forall g, {s : Strat | s2g s=g /\ SPE OcPref s}. 

Proof. 
intros. pose  (fun a => LETS (OcPref a) (UsedOutcomes g)). 
assert (forall a, rel_dec (r a)). intro. unfold r. apply LETS_dec. apply Outcome_dec.  
apply H. exists (BI r H1 g). split. apply BI_s2g. apply SPE_order_inclusion with r. 
intro. pose (LETS_restricted). unfold is_restricted in i. rewrite (BI_s2g r H1 g). unfold r. 
apply LETS_sub_rel. apply BI_SPE with (UsedOutcomes g); unfold r; intros. 

destruct (LETS_irrefl (OcPref a) (UsedOutcomes g)(eq_dec_midex Outcome_dec)). 
apply H2. apply irreflexive_preserved with (clos_trans Outcome (OcPref a)). 
apply clos_trans_monotonic. apply sub_rel_restriction. apply H0. 

apply LETS_transitive. apply LETS_total. exact (eq_dec_midex Outcome_dec). 
exact (rel_dec_midex (H a)). apply incl_refl. 
Qed.

Lemma SPE_Eq : forall OcPref,
(forall a, rel_dec (OcPref a)) ->
(forall g : Game, {s : Strat | s2g s=g /\ SPE OcPref s}) -> 
forall g : Game, {s : Strat | s2g s=g /\ Eq OcPref s}.  

Proof.
intros. destruct (H0 g). exists x. split. tauto. apply SPE_is_Eq. tauto. 
Qed. 

Lemma Eq_acyclic : forall OcPref,
(forall a, rel_dec (OcPref a)) ->
(forall g : Game, {s : Strat | s2g s=g /\ Eq OcPref s}) -> 
forall a : Agent, irreflexive (clos_trans Outcome (OcPref a)). 

Proof. 
repeat intro. destruct (clos_trans_path H1). 

destruct x0. simpl in H1. destruct (H0 (gL x)). destruct a0. destruct x0. pose (H4 a (sL o)). apply n.
apply Conv_refl. inversion H3. unfold StratPref. simpl. assumption. destruct l; inversion H3. 

destruct (H0 (gN a (gL x)  (map (fun y => gL y) (o::x0)))). destruct a0. destruct x1. inversion H3. 

destruct l0. 

destruct l. inversion H3. pose (H4 a0 (sN a0 (nil : list Strat) s (l++(x1::nil)))). apply n. 
constructor. tauto. simpl. apply ListConv_refl. unfold StratPref. simpl. inversion H3. 
rewrite <- (map_s2g_gL_InducedOutcome (l++(x1::nil)) (o::x0)) in H2. destruct s. simpl. inversion H7.
apply (path_app_elim_right (OcPref a) (InducedOutcome x1) x  (map InducedOutcome l) nil x). 
rewrite (map_app l (x1::nil) InducedOutcome) in H2. simpl in H2. assumption. destruct l0; inversion H7. 
rewrite (map_app l (x1::nil) s2g). assumption.  

pose (H4 a0 (sN a0 (l++(x1::nil)) s l0)). apply n. constructor. tauto. rewrite (app_ass l (x1::nil) (s::l0)). 
simpl. apply ListConv_refl. unfold StratPref. simpl. 
destruct l. destruct x1; inversion H3. destruct s; inversion H8. simpl in H2|-* . tauto. 
destruct l; inversion H10. destruct l; inversion H7. 
inversion H3. 
rewrite <- (map_s2g_gL_InducedOutcome (l++x1::s::l0) (o::x0)) in H2. 
assert (is_path (OcPref a) (InducedOutcome x1) x (map InducedOutcome (s :: l0))). 
apply path_app_elim_right with (map InducedOutcome l) x. 
rewrite (map_app l (x1::s::l0) InducedOutcome) in H2. assumption. simpl in H5. tauto. 
simpl. rewrite <- H8. rewrite (map_app l (x1::s::l0) s2g). tauto.  
Qed. 

 
