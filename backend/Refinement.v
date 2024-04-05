Require Import Coq.Relations.Relation_Definitions RelationClasses.

Ltac clear_ctx :=
  repeat (match goal with
          | [H : _ \/ _ |- _ ] => 
            let Hl := fresh H in 
            let Hr := fresh H in
            destruct H as [Hl | Hr]
          | [H : _ /\ _ |- _ ] => 
            let Hl := fresh H in 
            let Hr := fresh H in
            destruct H as [Hl Hr]
          | [H : _ <-> _ |- _ ] => 
            let Hl := fresh H in 
            let Hr := fresh H in
            destruct H as [Hl Hr]
          | [H : exists (x : _), _ |- _ ] =>
            let x := fresh x in
            destruct H as [x H]
          | [H : ?P , H2 : ?P |- _ ] => clear H2
          | [H : (?a && ?b)%bool = true |- _] =>
          apply andb_prop in H
          end
          ).

#[local] Obligation Tactic := idtac.

Class Refinable (A : Type) : Type :=
  {
    refinement : relation A ;
    is_transitive : transitive A refinement;
    is_right_reflexive : forall a1 a2, refinement a1 a2 -> refinement a2 a2
  }.

Infix "⊑" := refinement (at level 70).

Arguments refinement : simpl never.

#[export] Instance refinableTransitive {A} `{Refinable A} : Transitive refinement := { transitivity := is_transitive }.

#[export] Program Instance refinableFun {A B} `{Refinable A} `{Refinable B} : Refinable (A -> B) :=
  {
    refinement f g := (forall a1 a2, a1 ⊑ a2 -> f a1 ⊑ g a2) /\ (forall a1 a2, a1 ⊑ a2 -> g a1 ⊑ g a2) ;
  }.
Next Obligation. 
  intros. intros f g h Hmono1 Hmono2; split; intros a1 a2 Hprec.
  edestruct Hmono1; eauto. 
  etransitivity; [ apply H1; eauto | apply Hmono2]. eapply is_right_reflexive in Hprec; eauto.
  edestruct Hmono2; clear_ctx; eauto.
Qed.
Next Obligation.  
  firstorder.
Qed.

Definition sp_fun {A B} `{Refinable A} `{Refinable B} (f : A -> B): (forall a1 a2, a1 ⊑ a2 -> f a1 ⊑ f a2) -> f ⊑ f.
Proof.
  intros; repeat split; eauto.
Qed.

#[export] Program Instance refinableProp : Refinable Prop :=
  {
    refinement P Q := P -> Q
  }.
Solve All Obligations with firstorder.

Class Complete (A : Type) `{Refinable A} :=
  {
    is_complete : A -> Prop ;
    is_complete_spec : forall a, is_complete a -> a ⊑ a ;
  }.

Arguments is_complete : simpl never.

#[export] Program Instance completeFun {A B} `{Complete A} `{Complete B} : Complete (A -> B) :=
  {
    is_complete f := f ⊑ f /\ forall a, is_complete a -> is_complete (f a) ;
    is_complete_spec := _;
  }.
Solve All Obligations with firstorder.

Lemma is_complete_const_fun : forall {A B} `{Complete A} `{Complete B} (b : B), is_complete b -> is_complete (fun _ : A => b).
Proof.  simpl; intros. red; cbn.   split.
  - unfold refinement; cbn. eapply is_complete_spec in H3; eauto.
  - eauto.
Qed.

#[export] Hint Resolve is_complete_const_fun : typeclass_instances.

Class Ground (A : Type) `{Refinable A} `{Complete A} : Type :=
  {
    is_complete_minimal : forall a, is_complete a -> forall a', a' ⊑ a -> a' = a
  }.



(* Makes refinable instances where the refinement relation is equality. *)
Definition mkEqRefinable (A : Type) : Refinable A :=
 {|
  refinement (x y : A) := x = y ;
  is_transitive := ltac:(unfold Relation_Definitions.transitive; try induction x; eauto; intros; subst; eauto);
  is_right_reflexive := ltac:(simpl; eauto) ;
  |}.

  
(* Makes complete instances where the complete predicate is always true. 
  The premise is just to reuse the definition for other types with eq refinement.
*)
Program Definition mkCompleteTrue (A : Type) (refEqA := mkEqRefinable A) : Complete A :=
  {|
    is_complete _:= True ;
    is_complete_spec := _
  |}.
Next Obligation. reflexivity. Qed.

Program Instance mkGroundTrue (A : Type) (refEqA := mkEqRefinable A) (compA := mkCompleteTrue A) : Ground A :=
  {|
    is_complete_minimal := _
  |}.
Next Obligation. eauto. Qed.

Tactic Notation "unfold_complete" "in" hyp(H) := unfold is_complete in H; cbn in H.
Tactic Notation "unfold_complete" := unfold is_complete; cbn.
Tactic Notation "unfold_refinement" := unfold refinement; cbn.
Tactic Notation "unfold_refinement" "in" hyp(H) := unfold refinement in H; cbn in H.
  
From Coq Require Import FunctionalExtensionality.

Section Monotonicity.
  Context {A} `{HAC : Complete A}.

  Class Monotonizable (P : A -> Prop) :=
    {
      monotone : A -> Prop;
      antitone : A -> Prop;
      is_monotone : forall a1 a2, a1 ⊑ a2 -> monotone a1 ⊑ monotone a2;
      is_antitone : forall a1 a2, a1 ⊑ a2 -> antitone a2 ⊑ antitone a1;
      complete_monotone_is_equivalent : forall (a : A), is_complete a -> monotone a <-> P a;
      complete_antitone_is_equivalent : forall (a : A), is_complete a -> antitone a <-> P a
    }.

  Arguments monotone P {Monotonizable} a. 
  Arguments antitone P {Monotonizable} a. 

  Corollary incompleteness_tolerance : forall (P : A -> Prop) {HP: Monotonizable P} (a1 a2 : A),
    is_complete a1 -> a1 ⊑ a2 -> P a1 -> monotone P a2.
  Proof.
    intros P HP a1 a2 Hac Hprec HP1.
    eapply HP.(is_monotone); try eapply Hprec; eauto.
    apply HP.(complete_monotone_is_equivalent); eauto.
  Qed.

  Obligation Tactic :=  try now intuition.

  #[export] Program Instance monotonizable_const (P : Prop) : Monotonizable (fun a => P) := {
      monotone := fun _ => P ;
      antitone := fun _ => P ;
    }.
  
  #[export] Program Instance monotonizable_eq {B} `{HB : Ground B}
    (g h : A -> B) (Hcg : is_complete g) (Hch : is_complete h)
    : Monotonizable (fun a => g a = h a) | 2
    := {
      monotone := fun a => exists b, b ⊑ g a /\ b ⊑ h a ;
      antitone := fun a => is_complete (g a) /\ g a = h a ; 
    }.
  Next Obligation.
    intros ? ? ? ? ? g h ? ? a1 a2 Hprec [b [? ?]].
    exists b. split.
    - transitivity (g a1) ; auto. eapply is_complete_spec in Hcg; edestruct Hcg; eauto.
    - transitivity (h a1) ; auto. eapply is_complete_spec in Hch; edestruct Hch; eauto.
  Qed.
  Next Obligation.
    intros ? ? ? ? ? g h ? ? a1 a2 Hprec [? ?].
    erewrite (is_complete_minimal _ H3 (g a1)).
    - split; eauto. rewrite H4 in H3.
      erewrite (is_complete_minimal _ H3 (h a1)); eauto.
      unfold_complete in Hch; destruct Hch as [Hhmono _].
      apply Hhmono; eauto.
    - unfold_complete in Hcg; destruct Hcg as [Hgmono _].
      apply Hgmono; eauto.
  Qed.
  Next Obligation.
    intros B ? ? ? ? g h Hcg Hch a Hca. split.
    - intros [b [Hb1 Hb2]]. destruct Hcg, Hch.
      eapply is_complete_minimal in Hb1; eauto.
      eapply is_complete_minimal in Hb2; eauto; subst.
      assumption.
    - intros ->. destruct Hch. eapply is_complete_spec in Hca.
      edestruct H3; eauto.
  Qed.
  Next Obligation.
    intros B ? ? ? ? g h Hcg Hch a Hca. split.
    - intros []; eauto.
    - intros ->; split; eauto. unfold_complete in Hch.
      destruct Hch as [_ Hch]; apply Hch; eauto.
  Qed.

#[export] Program Instance monotonizable_eq_2 {B} `{HB : Ground B}
    (g : A -> B) (Hcg : is_complete g) (b : B) : Monotonizable (fun a => g a = b) | 1 := {
      monotone := fun a => b ⊑ g a ;
      antitone := fun a => is_complete (g a) /\ g a = b ;
    }.
  Next Obligation.
    intros ? ? ? ? ? g [Hcg ?] b a1 a2 Hprec ?.
    transitivity (g a1); try apply Hcg; eauto.
  Qed.
  Next Obligation.
  intros ? ? ? ? ? g [Hcg ?] b a1 a2 Hprec [? ?].
  unfold_refinement in Hcg. edestruct Hcg as [Hmono ?]; eauto. eapply is_complete_minimal in Hmono; eauto.
  rewrite Hmono; eauto.
  Qed.
  Next Obligation.
    intros B ? ? ? ? g [? ?] ? a Hca. split; [intros Hbg | intros <-].
    - eapply is_complete_minimal in Hbg; eauto.
    - apply is_complete_spec; eauto.
  Qed.
  Next Obligation.
    intros B ? ? ? ? g [? ?] ? a Hca. split; [intros [? Hbg] | intros <-]; eauto.
  Qed.

  #[export] Program Instance monotonizable_eq_fun {B C} `{HB : Refinable B} `{HC : Refinable C}
    (g h : A -> B -> C) {Hmono : Monotonizable (fun a => forall b, g a b = h a b)} : Monotonizable (fun a => g a = h a) := {
      monotone := monotone _ ;
      antitone := antitone _ ;
    }.
  Next Obligation.
    intros B C HB HC g h Hmono a1 a2 Hprec Hmono1.
    eapply is_monotone; eauto.
  Qed.
  Next Obligation.
    intros B C HB HC g h Hmono a1 a2 Hprec Hmono1.
    eapply is_antitone; eauto.
  Qed.
  Next Obligation with eauto.
    intros B C HB HC g h Hmono a Hac; simpl; split; intros Hp.
    - apply functional_extensionality; intros b.
      eapply Hmono.(complete_monotone_is_equivalent)...
    - eapply complete_monotone_is_equivalent...
      intros b. rewrite Hp...
  Qed.
  Next Obligation with eauto.
    intros B C HB HC g h Hmono a Hac; simpl; split; intros Hp.
    - apply functional_extensionality; intros b.
      eapply Hmono.(complete_antitone_is_equivalent)...
    - eapply complete_antitone_is_equivalent...
      intros b; rewrite Hp...
  Qed.

  #[export] Program Instance monotonizable_forall {B} {P : B -> A -> Prop} `{HPB : forall b, Monotonizable (P b)} : Monotonizable (fun a => forall b, P b a) :=
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

  #[export] Program Instance monotonizable_exists {B} `{HB: Refinable B} {P : B -> A -> Prop} `{HPB : forall b, Monotonizable (P b)} : Monotonizable (fun a => exists b, P b a) :=
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

  #[export] Program Instance monotonizable_conj (P Q : A -> Prop) {HP : Monotonizable P} {HQ : Monotonizable Q} : Monotonizable (fun a => P a /\ Q a) :=
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

  #[export] Program Instance monotonizable_disj (P Q : A -> Prop) {HP : Monotonizable P} {HQ : Monotonizable Q} : Monotonizable (fun a => P a \/ Q a) :=
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

  #[export] Program Instance monotonizable_arrow {P Q : A -> Prop} {HP : Monotonizable P} {HQ : Monotonizable Q} : Monotonizable (fun a => P a -> Q a) :=
    {
      monotone := fun a => antitone P a -> monotone Q a ;
      antitone := fun a => monotone P a -> antitone Q a ;
    }.
  Next Obligation.
    simpl; intros P Q HP HQ a1 a2 Hprec ? Hanti.
    eapply HQ.(is_monotone).
    - apply Hprec.
    - apply H0. eapply HP.(is_antitone); eauto.
  Qed.
  Next Obligation.
    simpl; intros P Q HP HQ a1 a2 Hprec ? Hanti.
    eapply HQ.(is_antitone).
    - apply Hprec.
    - apply H0. eapply HP.(is_monotone); try apply Hprec; eauto.
  Qed.
  Next Obligation with eauto.
    simpl; intros P Q HP HQ a Ha; split; intros ?.
    - intros H1. eapply HQ.(complete_monotone_is_equivalent); eauto.
      apply H0. eapply HP.(complete_antitone_is_equivalent); eauto.
    - intros H1. eapply HQ.(complete_monotone_is_equivalent); eauto.
      apply H0. eapply HP.(complete_antitone_is_equivalent); eauto.
  Qed.
  Next Obligation with eauto.
    simpl; intros P Q HP HQ a Ha; split; intros ?.
    - intros H1. eapply HQ.(complete_antitone_is_equivalent); eauto.
      apply H0. eapply HP.(complete_monotone_is_equivalent); eauto.
    - intros H1. eapply HQ.(complete_antitone_is_equivalent); eauto.
      apply H0. eapply HP.(complete_monotone_is_equivalent); eauto.
  Qed.

 #[export] Program Instance monotonizable_refinement {B} `{Ground B}
   (g : A -> B) (Hcg : is_complete g) (b : B) (Hb : is_complete b) : Monotonizable (fun a => g a ⊑ b) := {
      monotone := fun a => b ⊑ g a ;
      antitone := fun a => g a ⊑ b ;
    }.
  Next Obligation.
    intros ? ? ? ? ? g ? b ? a1 a2 Hprec ?; cbn. 
    transitivity (g a1); eauto.
    apply Hcg; eauto.
  Qed.
  Next Obligation.
    intros ? ? ? ? ? g ? b ? a1 a2 Hprec ?; cbn.
    transitivity (g a2); eauto.
    apply Hcg; eauto.
  Qed.
  Next Obligation.
    intros B ? ? ? ? g ? ? ? a Hca.
    split; intros Hbg; pose proof (Hbg' := Hbg); eapply is_complete_minimal in Hbg; eauto; try rewrite Hbg.
    - eapply is_right_reflexive; eauto.
    - apply Hcg; eauto.
    - eapply is_right_reflexive; eauto.
  Qed.

End Monotonicity.

Arguments monotone {A H HAC} P {Monotonizable} _. 
Arguments antitone {A H HAC} P {Monotonizable} _. 

#[export] Hint Extern 0 (Complete _) => eassumption : typeclass_instances.

Lemma fun_is_complete_if_complete_dom : forall {A B} `{Complete A} `{Complete B},
    forall a, is_complete a -> is_complete (fun f : A -> B => f a).
Proof.
  simpl; intros; split.
  - unfold refinement; cbn. split; intros; edestruct H4; eauto; eapply is_complete_spec in H3; eauto.
  - intros. destruct H4. eauto.
Qed.

#[export] Hint Resolve fun_is_complete_if_complete_dom : typeclass_instances.
Lemma monotonizable_equiv : forall A `{Complete A} (P Q : A -> Prop) , Monotonizable P -> (forall a, P a <-> Q a) -> Monotonizable Q.
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

#[export] Instance refinable_bool : Refinable bool := mkEqRefinable bool.
#[export] Instance complete_bool : Complete bool := mkCompleteTrue bool.
#[export] Instance ground_bool : Ground bool := mkGroundTrue bool.

Hint Extern 0 (@is_complete ?A (mkEqRefinable _) (mkCompleteTrue _) _) =>
exact I
:  typeclass_instances.

Hint Extern 0 (@is_complete ?A ?B ?C _) => unfold B; unfold C
:  typeclass_instances.

