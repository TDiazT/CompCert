Require Import Coq.Relations.Relation_Definitions RelationClasses.
From Coq Require Import FunctionalExtensionality.

#[local] Obligation Tactic := idtac.

(***********************************)
(*          Refinable              *)
(***********************************)
Class Refinable (A : Type) : Type :=
  {
    refinement : relation A ;
    is_transitive : transitive A refinement;
    is_reflexive : reflexive A refinement
  }.

Infix "⊑" := refinement (at level 70).

Arguments refinement : simpl never.

Tactic Notation "unfold_refinement" := unfold refinement; cbn.
Tactic Notation "unfold_refinement" "in" hyp(H) := unfold refinement in H; cbn in H.

#[export] 
Instance refinableTransitive {A} `{Refinable A} : Transitive refinement := { transitivity := is_transitive }.
#[export] 
Instance refinableReflexive {A} `{Refinable A} : Reflexive refinement := { reflexivity := is_reflexive }.

#[export] 
Program Instance refinableFun {A B} `{Refinable A} `{Refinable B} : Refinable (A -> B) :=
  {
    refinement f g := forall a, f a ⊑ g a ;
  }.
Next Obligation. 
  red; intros; etransitivity; eauto. 
Qed.
Next Obligation.
  red; intros; reflexivity. 
Qed.

(***********************************)
(*          Monotonous             *)
(***********************************)
Definition is_monotonous {A B} `{Refinable A} `{Refinable B} (f : A -> B) := 
    forall a1 a2, a1 ⊑ a2 -> f a1 ⊑ f a2.

Lemma fun_is_monotonous : forall {A B} `{Refinable A} `{Refinable B},
    forall a, is_monotonous (fun f : A -> B => f a).
Proof.
  red; simpl; intros; eauto.
Qed.

Existing Class is_monotonous.

#[export] Hint Resolve fun_is_monotonous : typeclass_instances.
    
(***********************************)
(*          Complete               *)
(***********************************)
Class Complete (A : Type) :=
  {
    is_complete : A -> Prop ;
  }.

Arguments is_complete : simpl never.

Tactic Notation "unfold_complete" "in" hyp(H) := unfold is_complete in H; cbn in H.
Tactic Notation "unfold_complete" := unfold is_complete; cbn.

#[export] Hint Extern 0 (Complete _) => eassumption : typeclass_instances.
#[export] Hint Extern 0 (@is_complete ?A ?B _) => unfold B :  typeclass_instances.

#[export] 
Instance completeFun {A B} `{Complete A} `{Complete B} : Complete (A -> B) :=
  {
    is_complete f := forall a, is_complete a -> is_complete (f a) ;
  }.


Lemma apply_complete : forall {A B} `{Complete A} `{Complete B},
    forall a, is_complete a -> is_complete (fun f : A -> B => f a).
Proof.
  red; simpl; intros; eauto.
Qed.

#[export] Hint Resolve apply_complete : typeclass_instances.

Lemma is_complete_const_fun : forall {A B} `{Complete A} `{Complete B} (b : B), 
  is_complete b -> is_complete (fun _ : A => b).
Proof. 
  intros ? ? ? ? ? ? b Hb. red; cbn. intros; eauto.
Qed.

#[export] Hint Resolve is_complete_const_fun : typeclass_instances.

(***********************************)
(*          Ground                 *)
(***********************************)
Class Ground (A : Type) `{Refinable A} `{Complete A} :=
  {
    is_complete_minimal : forall a, is_complete a -> forall a', a' ⊑ a -> a' = a
  }.


(***********************************)
(*          Equality instances     *)
(***********************************)
(* Defining equality as a "default" refinement relation. *)
#[export]
Instance eqRefinable (A : Type) : Refinable A | 100 :=
 {|
  refinement := eq ;
  is_transitive := ltac:(unfold transitive; etransitivity; eauto);
  is_reflexive := ltac:(red; intros; reflexivity) ;
 |}.

  
(* Makes complete instances where the complete predicate is always true. 
  The premise is just to reuse the definition for other types with eq refinement.
*)
#[export]
Instance eqCompleteTrue (A : Type) : Complete A | 100 :=
  {|
    is_complete _ := True ;
  |}.

#[export]
Hint Extern 0 (@is_complete ?A (eqCompleteTrue _) _) =>
exact I
:  typeclass_instances.


#[export]
Instance eqGroundTrue (A : Type) (refEqA := eqRefinable A) (compA := eqCompleteTrue A) : Ground A.
Proof. econstructor. eauto. Qed.

  

Section Monotonicity.
  Context {A} {HA: Refinable A} {HAC : Complete A}.

  Class Monotonizable (P : A -> Prop) :=
    {
      monotone : A -> Prop;
      antitone : A -> Prop;
      is_monotone : forall a1 a2, a1 ⊑ a2 -> monotone a1 -> monotone a2;
      is_antitone : forall a1 a2, a1 ⊑ a2 -> antitone a2 -> antitone a1;
      complete_monotone_is_equivalent : forall (a : A), is_complete a -> monotone a <-> P a;
      complete_antitone_is_equivalent : forall (a : A), is_complete a -> antitone a <-> P a
    }.

  Arguments monotone P {Monotonizable} a. 
  Arguments antitone P {Monotonizable} a. 


  Obligation Tactic :=  try now eauto.

  #[export] 
  Program Instance monotonizableConst (P : Prop) : Monotonizable (fun a => P) := {
      monotone := fun _ => P ;
      antitone := fun _ => P ;
    }.
  
  Obligation Tactic :=  try now intuition.

  #[export] 
  Program Instance monotonizableEq {B} `{HB : Ground B}
    (g h : A -> B) (Hcg : is_monotonous g) (Hch : is_monotonous h)
    (Hcg' : is_complete g) (Hch' : is_complete h)
    : Monotonizable (fun a => g a = h a) | 2
    := {
      monotone := fun a => exists b, b ⊑ g a /\ b ⊑ h a ;
      antitone := fun a => is_complete (g a) /\ g a = h a ; 
    }.
  Next Obligation.
    intros ? ? ? ? g h ? ? ? ? a1 a2 Hprec [b [? ?]].
    exists b. split.
    - transitivity (g a1) ; auto. 
    - transitivity (h a1) ; auto.
  Qed.
  Next Obligation.
    intros ? ? ? ? g h ? ? ? ? a1 a2 Hprec [Hgc Heq].
    erewrite (is_complete_minimal _ Hgc (g a1)).
    - split; eauto. rewrite Heq in Hgc.
      erewrite (is_complete_minimal _ Hgc (h a1)); eauto.
    - eauto.
  Qed.
  Next Obligation.
    intros B ? ? ? g h ? ? Hcg Hch a Hca. split.
    - intros [b [Hb1 Hb2]].
      eapply is_complete_minimal in Hb1; eauto.
      eapply is_complete_minimal in Hb2; eauto; subst.
      assumption.
    - intros ->. eexists; split; reflexivity.
  Qed.

  #[export] 
  Program Instance monotonizableEqL {B} `{HB : Ground B}
    (g : A -> B) (Hcg : is_complete g) (Hmonog : is_monotonous g) 
    (b : B) : Monotonizable (fun a => g a = b) | 1 := {
      monotone := fun a => b ⊑ g a ;
      antitone := fun a => is_complete (g a) /\ g a = b ;
    }.
  Next Obligation.
    cbn; intros ? ? ? ? g Hcg ? b a1 a2 Hprec ?.
    transitivity (g a1); try apply Hcg; eauto.
  Qed.
  Next Obligation.
    intros ? ? ? ? g ? Hmono b a1 a2 Hprec [? ?]. 
    eapply is_complete_minimal in Hmono; eauto.
    rewrite Hmono; eauto.
  Qed.
  Next Obligation.
    intros B ? ? ? g ? ? ? a Hca. split; [intros Hbg | intros <-].
    - eapply is_complete_minimal in Hbg; eauto.
    - reflexivity.
  Qed.

  #[export] 
  Program Instance monotonizableForall {B} {P : B -> A -> Prop} `{HPB : forall b, Monotonizable (P b)} :      
    Monotonizable (fun a => forall b, P b a) :=
    {
      monotone := fun a => forall b, monotone (P b) a ;
      antitone := fun a => forall b, antitone (P b) a ;
    }.
  Next Obligation.
    intros B P HPB a1 a2 Hprec Hmono; simpl; intros b.
    eapply is_monotone.
    - apply Hprec.
    - eauto.
  Qed.
  Next Obligation.
    intros B P HPB a1 a2 Hprec Hmono; simpl; intros b.
    eapply is_antitone.
    - apply Hprec.
    - apply Hmono.
  Qed.
  Next Obligation with eauto.
    intros B P HPB a Hac; simpl; split; intros HP b; eapply (HPB b).(complete_monotone_is_equivalent)...
  Qed.
  Next Obligation with eauto.
    intros B P HPB a Hac; simpl; split; intros HP b; eapply (HPB b).(complete_antitone_is_equivalent)...
  Qed.

  #[export] 
  Program Instance monotonizableExists {B} `{HB: Refinable B} 
    {P : B -> A -> Prop} `{HPB : forall b, Monotonizable (P b)} 
    : Monotonizable (fun a => exists b, P b a) :=
    {
      monotone := fun a => exists b, monotone (P b) a ;
      antitone := fun a => exists b, antitone (P b) a ;
    }.
  Next Obligation.
    intros B HB P HPB a1 a2 Hprec [b HP]; simpl.
    exists b; eapply is_monotone; try apply Hprec; eauto.
  Qed.
  Next Obligation.
    intros B HB P HPB a1 a2 Hprec [b HP]; simpl.
    exists b; eapply is_antitone; try apply Hprec; eauto.
  Qed.
  Next Obligation with eauto.
    intros B HB P HPB a Hac; simpl; split; intros [b HP]; exists b;
      eapply (HPB b).(complete_monotone_is_equivalent)...
  Qed.
  Next Obligation with eauto.
    intros B HB P HPB a Hac; simpl; split; intros [b HP]; exists b;
      eapply (HPB b).(complete_antitone_is_equivalent)...
  Qed.

  #[export] 
  Program Instance monotonizableConj (P Q : A -> Prop) {HP : Monotonizable P} {HQ : Monotonizable Q} :  
    Monotonizable (fun a => P a /\ Q a) :=
    {
      monotone := fun a => (monotone P a) /\ (monotone Q a) ;
      antitone := fun a => (antitone P a) /\ (antitone Q a) ;
    }.
  Next Obligation.
    intros P Q HP HQ a1 a2 Hprec [HP1 HQ1]; simpl; split.
    - eapply is_monotone; try apply Hprec; eauto.
    - eapply is_monotone; try apply Hprec; eauto.
  Qed.
  Next Obligation.
    intros P Q HP HQ a1 a2 Hprec [HP1 HQ1]; simpl; split.
    - eapply is_antitone; try apply Hprec; eauto.
    - eapply is_antitone; try apply Hprec; eauto.
  Qed.
  Next Obligation with eauto.
    intros P Q HP HQ a Hac; simpl; split; intros [HP1 HQ1]; split; try eapply complete_monotone_is_equivalent...
  Qed.
  Next Obligation with eauto.
    intros P Q HP HQ a Hac; simpl; split; intros [HP1 HQ1]; split; try eapply complete_antitone_is_equivalent...
  Qed.

  #[export] 
  Program Instance monotonizableDisj (P Q : A -> Prop) {HP : Monotonizable P} {HQ : Monotonizable Q} : 
    Monotonizable (fun a => P a \/ Q a) :=
    {
      monotone := fun a => (monotone P a) \/ (monotone Q a) ;
      antitone := fun a => (antitone P a) \/ (antitone Q a) ;
    }.
  Next Obligation.
    intros P Q HP HQ a1 a2 Hprec [HP1 | HQ1]; simpl.
    - left; eapply is_monotone; try apply Hprec; eauto.
    - right; eapply is_monotone; try apply Hprec; eauto.
  Qed.
  Next Obligation.
    intros P Q HP HQ a1 a2 Hprec [HP1 | HQ1]; simpl.
    - left; eapply is_antitone; try apply Hprec; eauto.
    - right; eapply is_antitone; try apply Hprec; eauto.
  Qed.
  Next Obligation with eauto.
    intros P Q HP HQ a Hac; simpl; split; intros [HP1 | HQ1];
      try (now left; apply complete_monotone_is_equivalent; eauto);
      try (now right; apply complete_monotone_is_equivalent; eauto).
  Qed.
  Next Obligation with eauto.
    intros P Q HP HQ a Hac; simpl; split; intros [HP1 | HQ1];
      try (now left; apply complete_antitone_is_equivalent; eauto);
      try (now right; apply complete_antitone_is_equivalent; eauto).
  Qed.

  #[export] 
  Program Instance monotonizableArrow {P Q : A -> Prop} {HP : Monotonizable P} {HQ : Monotonizable Q} : 
    Monotonizable (fun a => P a -> Q a) :=
    {
      monotone := fun a => antitone P a -> monotone Q a ;
      antitone := fun a => monotone P a -> antitone Q a ;
    }.
  Next Obligation.
    simpl; intros P Q HP HQ a1 a2 Hprec ? Hanti.
    eapply HQ.(is_monotone).
    - apply Hprec.
    - apply H. eapply HP.(is_antitone); eauto.
  Qed.
  Next Obligation.
    simpl; intros P Q HP HQ a1 a2 Hprec ? Hanti.
    eapply HQ.(is_antitone).
    - apply Hprec.
    - apply H. eapply HP.(is_monotone); try apply Hprec; eauto.
  Qed.
  Next Obligation with eauto.
    simpl; intros P Q HP HQ a Ha; split; intros ?.
    - intros H1. eapply HQ.(complete_monotone_is_equivalent); eauto.
      apply H. eapply HP.(complete_antitone_is_equivalent); eauto.
    - intros H1. eapply HQ.(complete_monotone_is_equivalent); eauto.
      apply H. eapply HP.(complete_antitone_is_equivalent); eauto.
  Qed.
  Next Obligation with eauto.
    simpl; intros P Q HP HQ a Ha; split; intros ?.
    - intros H1. eapply HQ.(complete_antitone_is_equivalent); eauto.
      apply H. eapply HP.(complete_monotone_is_equivalent); eauto.
    - intros H1. eapply HQ.(complete_antitone_is_equivalent); eauto.
      apply H. eapply HP.(complete_monotone_is_equivalent); eauto.
  Qed.

End Monotonicity.

Arguments monotone {A HA HAC} P {Monotonizable} _. 
Arguments antitone {A HA HAC} P {Monotonizable} _. 

Lemma monotonizable_equiv : forall A `{Refinable A} `{Complete A} (P Q : A -> Prop) , 
  Monotonizable P -> 
  (forall a, P a <-> Q a) -> 
  Monotonizable Q.
Proof.
  intros A HAR HAC P Q HPmono Hequiv.
  unshelve econstructor.
  - exact (monotone P).
  - exact (antitone P).
  - eapply HPmono.(is_monotone).
  - eapply HPmono.(is_antitone).
  - intros a Hac; split.
    * intros HPa. apply Hequiv. eapply HPmono.(complete_monotone_is_equivalent); eauto.
    * intros HQa. apply Hequiv in HQa. eapply HPmono.(complete_monotone_is_equivalent); eauto.
  - intros a Hac; split.
    * intros HPa. apply Hequiv. eapply HPmono.(complete_antitone_is_equivalent); eauto.
    * intros HQa. apply Hequiv in HQa. eapply HPmono.(complete_antitone_is_equivalent); eauto.
Qed.

#[export] 
Instance monotonizable_eq_fun {A} `{Refinable A} `{Complete A} 
  {B} `{Refinable B} 
  {C} `{Refinable C}
  (g h : A -> B -> C) {Hmono : Monotonizable (fun a => forall b, g a b = h a b)} 
  : Monotonizable (fun a => g a = h a).
Proof.
  eapply monotonizable_equiv.
  - apply Hmono.
  - intros a; split.
    * intros Heq. apply functional_extensionality; eauto.
    * intros ->; eauto. 
Defined.