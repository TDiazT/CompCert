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
Definition is_monotone {A B} `{Refinable A} `{Refinable B} (f : A -> B) := 
    forall a1 a2, a1 ⊑ a2 -> f a1 ⊑ f a2.

Lemma fun_is_monotone : forall {A B} `{Refinable A} `{Refinable B},
    forall a, is_monotone (fun f : A -> B => f a).
Proof.
  red; simpl; intros; eauto.
Qed.

Existing Class is_monotone.

#[export] Hint Resolve fun_is_monotone : typeclass_instances.
    
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
Instance eqGroundTrue (A : Type) (refEqA := eqRefinable A) (compA := eqCompleteTrue A) : Ground A | 100.
Proof. econstructor. eauto. Qed.

  

Section IncReformulation.
  Context {A} {HA: Refinable A} {HAC : Complete A}.

  Class IncRef (P : A -> Prop) :=
    {
      ir_mono : A -> Prop;
      ir_anti : A -> Prop;
      is_monotone_mono : forall a1 a2, a1 ⊑ a2 -> ir_mono a1 -> ir_mono a2;
      is_antitone_anti : forall a1 a2, a1 ⊑ a2 -> ir_anti a2 -> ir_anti a1;
      approx_mono : forall a, P a -> ir_mono a;
      approx_anti : forall a, ir_anti a -> P a;
      recoverability_mono : forall (a : A), is_complete a -> ir_mono a -> P a;
      recoverability_anti : forall (a : A), is_complete a -> P a -> ir_anti a
      }.

  Arguments ir_mono P {IncRef} a. 
  Arguments ir_anti P {IncRef} a. 

  Lemma complete_monotone_is_equivalent {P} `{IncRef P} : forall (a : A), is_complete a -> ir_mono P a <-> P a.
  Proof.
    intros; split; [ apply recoverability_mono; eauto | apply approx_mono].
  Qed.

  Lemma complete_antitone_is_equivalent {P} `{IncRef P} : forall (a : A), is_complete a -> ir_anti P a <-> P a.
  Proof.
    intros; split; [ apply approx_anti | apply recoverability_anti; eauto].
  Qed.

  Obligation Tactic :=  try now eauto.

  #[export] 
  Program Instance IncRefConst (P : Prop) : IncRef (fun a => P) := {
      ir_mono := fun _ => P ;
      ir_anti := fun _ => P ;
    }.
  
  Obligation Tactic :=  try now intuition.

  #[export] 
  Program Instance IncRefEq {B} `{HB : Ground B}
    (f g : A -> B) (Hcf : is_monotone f) (Hcg : is_monotone g)
    (Hcf' : is_complete f) (Hcg' : is_complete g)
    : IncRef (fun a => f a = g a) | 2
    := {
      ir_mono := fun a => exists b, b ⊑ f a /\ b ⊑ g a ;
      ir_anti := fun a => is_complete (f a) /\ f a = g a ; 
    }.
  Next Obligation.
    intros ? ? ? ? f g ? ? ? ? a1 a2 Hprec [b [? ?]].
    exists b. split.
    - transitivity (f a1) ; auto. 
    - transitivity (g a1) ; auto.
  Qed.
  Next Obligation.
    intros ? ? ? ? f g ? ? ? ? a1 a2 Hprec [Hfc Heq].
    erewrite (is_complete_minimal _ Hfc (f a1)); eauto.
    split; eauto. rewrite Heq in Hfc.
    erewrite (is_complete_minimal _ Hfc (g a1)); eauto.
  Qed.
  Next Obligation.
  intros ? ? ? ? ? ? ? ? ? ? ? Hca.
  cbn in *. eexists. split; try reflexivity. rewrite Hca; reflexivity.  
  Qed. 
  Next Obligation.
    intros ? ? ? ? ? ? ? ? ? ? ? ?.
    intros [b [Hb1 Hb2]].
    eapply is_complete_minimal in Hb1; eauto.
    eapply is_complete_minimal in Hb2; eauto; subst.
    assumption.
  Qed.

  #[export] 
  Program Instance IncRefEqL {B} `{HB : Ground B}
    (f : A -> B) (Hcf : is_complete f) (Hmonof : is_monotone f) 
    (b : B) : IncRef (fun a => f a = b) | 1 := {
      ir_mono := fun a => b ⊑ f a ;
      ir_anti := fun a => is_complete (f a) /\ f a = b ;
    }.
  Next Obligation.
    cbn; intros ? ? ? ? f Hcf ? ? ? ? ? ?.
    transitivity (f a1); try apply Hcf; eauto.
  Qed.
  Next Obligation.
    intros ? ? ? ? ? ? Hmono b a1 a2 Hprec [? ?]. 
    eapply is_complete_minimal in Hmono; eauto.
    rewrite Hmono; eauto.
  Qed.
  Next Obligation.
    intros B ? ? ? ? ? ? ? a <-. reflexivity.
  Qed.
  Next Obligation.
    intros B ? ? ? ? ? ? ? ? ? ?.
    cbn. symmetry. eapply is_complete_minimal; eauto.
  Qed.

  #[export] 
  Program Instance IncRefForall {B} {P : B -> A -> Prop} `{HPB : forall b, IncRef (P b)} :      
    IncRef (fun a => forall b, P b a) :=
    {
      ir_mono := fun a => forall b, ir_mono (P b) a ;
      ir_anti := fun a => forall b, ir_anti (P b) a ;
    }.
  Next Obligation.
    intros B P HPB a1 a2 Hprec Hmono; simpl; intros b.
    eapply is_monotone_mono.
    - apply Hprec.
    - eauto.
  Qed.
  Next Obligation.
    intros B P HPB a1 a2 Hprec Hmono; simpl; intros b.
    eapply is_antitone_anti.
    - apply Hprec.
    - apply Hmono.
  Qed.
  Next Obligation with eauto.
    intros B P HPB a Hac; simpl in *. intros b; eapply (HPB b).(approx_mono)...
  Qed.
  Next Obligation with eauto.
    intros B P HPB a Hac; simpl in *. intros b; eapply (HPB b).(approx_anti)...
  Qed.
  Next Obligation with eauto.
    intros B P HPB a Hac; simpl; intros HP b; eapply complete_monotone_is_equivalent...
  Qed.
  Next Obligation with eauto.
    intros B P HPB a Hac; simpl; intros HP b; eapply complete_antitone_is_equivalent...
  Qed.

  #[export] 
  Program Instance IncRefExists {B} `{HB: Refinable B} 
    {P : B -> A -> Prop} `{HPB : forall b, IncRef (P b)} 
    : IncRef (fun a => exists b, P b a) :=
    {
      ir_mono := fun a => exists b, ir_mono (P b) a ;
      ir_anti := fun a => exists b, ir_anti (P b) a ;
    }.
  Next Obligation.
    intros B HB P HPB a1 a2 Hprec [b HP]; simpl.
    exists b; eapply is_monotone_mono; try apply Hprec; eauto.
  Qed.
  Next Obligation.
    intros B HB P HPB a1 a2 Hprec [b HP]; simpl.
    exists b; eapply is_antitone_anti; try apply Hprec; eauto.
  Qed.
  Next Obligation with eauto.
    intros B HB P HPB a ; simpl in *; intros [b HP]; exists b;
      eapply (HPB b).(approx_mono)...
  Qed.
  Next Obligation with eauto.
    intros B HB P HPB a ; simpl in *; intros [b HP]; exists b;
      eapply (HPB b).(approx_anti)...
  Qed.
  Next Obligation with eauto.
    intros B HB P HPB a Hac; simpl; intros [b HP]; exists b;
      eapply complete_monotone_is_equivalent...
  Qed.
  Next Obligation with eauto.
    intros B HB P HPB a Hac; simpl; intros [b HP]; exists b;
      eapply complete_antitone_is_equivalent...
  Qed.

  #[export] 
  Program Instance IncRefConj (P Q : A -> Prop) {HP : IncRef P} {HQ : IncRef Q} :  
    IncRef (fun a => P a /\ Q a) :=
    {
      ir_mono := fun a => (ir_mono P a) /\ (ir_mono Q a) ;
      ir_anti := fun a => (ir_anti P a) /\ (ir_anti Q a) ;
    }.
  Next Obligation.
    intros P Q HP HQ a1 a2 Hprec [HP1 HQ1]; simpl; split.
    - eapply is_monotone_mono; try apply Hprec; eauto.
    - eapply is_monotone_mono; try apply Hprec; eauto.
  Qed.
  Next Obligation.
    intros P Q HP HQ a1 a2 Hprec [HP1 HQ1]; simpl; split.
    - eapply is_antitone_anti; try apply Hprec; eauto.
    - eapply is_antitone_anti; try apply Hprec; eauto.
  Qed.
  Next Obligation with eauto.
    intros P Q HP HQ a; simpl in *; intros [HP1 HQ1]. split; try eapply approx_mono...
  Qed.
  Next Obligation with eauto.
    intros P Q HP HQ a; simpl in *; intros [HP1 HQ1]. split; try eapply approx_anti...
  Qed.
  Next Obligation with eauto.
    intros P Q HP HQ a Hac; simpl; intros [HP1 HQ1]; split; try eapply complete_monotone_is_equivalent...
  Qed.
  Next Obligation with eauto.
    intros P Q HP HQ a Hac; simpl; intros [HP1 HQ1]; split; try eapply complete_antitone_is_equivalent...
  Qed.

  #[export] 
  Program Instance IncRefDisj (P Q : A -> Prop) {HP : IncRef P} {HQ : IncRef Q} : 
    IncRef (fun a => P a \/ Q a) :=
    {
      ir_mono := fun a => (ir_mono P a) \/ (ir_mono Q a) ;
      ir_anti := fun a => (ir_anti P a) \/ (ir_anti Q a) ;
    }.
  Next Obligation.
    intros P Q HP HQ a1 a2 Hprec [HP1 | HQ1]; simpl.
    - left; eapply is_monotone_mono; try apply Hprec; eauto.
    - right; eapply is_monotone_mono; try apply Hprec; eauto.
  Qed.
  Next Obligation.
    intros P Q HP HQ a1 a2 Hprec [HP1 | HQ1]; simpl.
    - left; eapply is_antitone_anti; try apply Hprec; eauto.
    - right; eapply is_antitone_anti; try apply Hprec; eauto.
  Qed.
  Next Obligation with eauto.
    intros P Q HP HQ a; simpl in *; intros [HP1 | HQ1];
      try (now left; apply approx_mono; eauto);
      try (now right; apply approx_mono; eauto).
  Qed.
  Next Obligation with eauto.
    intros P Q HP HQ a; simpl in *; intros [HP1 | HQ1];
      try (now left; apply approx_anti; eauto);
      try (now right; apply approx_anti; eauto).
  Qed.
  Next Obligation with eauto.
    intros P Q HP HQ a Hac; simpl; intros [HP1 | HQ1];
      try (now left; apply complete_monotone_is_equivalent; eauto);
      try (now right; apply complete_monotone_is_equivalent; eauto).
  Qed.
  Next Obligation with eauto.
    intros P Q HP HQ a Hac; simpl; intros [HP1 | HQ1];
      try (now left; apply complete_antitone_is_equivalent; eauto);
      try (now right; apply complete_antitone_is_equivalent; eauto).
  Qed.

  #[export] 
  Program Instance IncRefArrow {P Q : A -> Prop} {HP : IncRef P} {HQ : IncRef Q} : 
    IncRef (fun a => P a -> Q a) :=
    {
      ir_mono := fun a => ir_anti P a -> ir_mono Q a ;
      ir_anti := fun a => ir_mono P a -> ir_anti Q a ;
    }.
  Next Obligation.
    simpl; intros P Q HP HQ a1 a2 Hprec ? Hanti.
    eapply HQ.(is_monotone_mono).
    - apply Hprec.
    - apply H. eapply HP.(is_antitone_anti); eauto.
  Qed.
  Next Obligation.
    simpl; intros P Q HP HQ a1 a2 Hprec ? Hanti.
    eapply HQ.(is_antitone_anti).
    - apply Hprec.
    - apply H. eapply HP.(is_monotone_mono); try apply Hprec; eauto.
  Qed.
  Next Obligation with eauto.
    simpl; intros P Q HP HQ a Hf Ha.
    now eapply approx_mono, Hf, approx_anti.
  Qed.
  Next Obligation with eauto.
    simpl; intros P Q HP HQ a Hf Ha.
    now eapply approx_anti, Hf, approx_mono.
  Qed.
  Next Obligation with eauto.
    simpl; intros P Q HP HQ a Ha; intros ?.
    - intros H1. eapply complete_monotone_is_equivalent; eauto.
      apply H. eapply complete_antitone_is_equivalent; eauto.
  Qed.
  Next Obligation with eauto.
    simpl; intros P Q HP HQ a Ha; intros ?.
    - intros H1. eapply (complete_antitone_is_equivalent); eauto.
      apply H. eapply (complete_monotone_is_equivalent); eauto.
  Qed.

End IncReformulation.

Arguments ir_mono {A HA HAC} P {IncRef} _. 
Arguments ir_anti {A HA HAC} P {IncRef} _. 

Lemma IncRefEquiv : forall A `{Refinable A} `{Complete A} (P Q : A -> Prop) , 
  IncRef P -> 
  (forall a, P a <-> Q a) -> 
  IncRef Q.
Proof.
  intros A HAR HAC P Q HPmono Hequiv.
  unshelve econstructor.
  - exact (ir_mono P).
  - exact (ir_anti P).
  - eapply HPmono.(is_monotone_mono).
  - eapply HPmono.(is_antitone_anti).
  - intros a Ha. now eapply approx_mono, Hequiv. 
  - intros a Ha. now eapply Hequiv, approx_anti. 
  - intros a Hac.
    * intros HPa. apply Hequiv. eapply (complete_monotone_is_equivalent); eauto.
  - intros a Hac.
    * intros HQa. apply Hequiv in HQa. eapply (complete_antitone_is_equivalent); eauto.
Qed.

#[export] 
Instance IncRefEq_fun {A} `{Refinable A} `{Complete A} 
  {B} `{Refinable B} 
  {C} `{Refinable C}
  (f g : A -> B -> C) {Hmono : IncRef (fun a => forall b, f a b = g a b)} 
  : IncRef (fun a => f a = g a).
Proof.
  eapply IncRefEquiv.
  - apply Hmono.
  - intros; split.
    * intros. apply functional_extensionality; eauto.
    * intros ->; eauto. 
Defined.