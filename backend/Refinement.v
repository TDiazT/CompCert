Require Import Auto.
Require Import Coq.Relations.Relation_Definitions.

Class Refinable (A : Type) : Type :=
  {
    is_refinement : relation A ;
    is_transitive : transitive A is_refinement;
    is_right_reflexive : forall a1 a2, is_refinement a1 a2 -> is_refinement a2 a2
  }.

Infix "⊑" := is_refinement (at level 70).

Arguments is_refinement : simpl never.

#[export, refine] Instance refinableFun {A B} `{Refinable A} `{Refinable B} : Refinable (A -> B) :=
  {
    is_refinement f g := forall a1 a2, a1 ⊑ a2 -> f a1 ⊑ g a2 /\ f a1 ⊑ f a2 /\ g a1 ⊑ g a2 ;
  }.
Proof.
  - intros f g h Hmono1 Hmono2 a1 a2 Hprec; split.
    edestruct Hmono1; eauto.
    eapply is_transitive; [ apply H1 | apply Hmono2]. eapply is_right_reflexive in Hprec; eauto.
    split. edestruct Hmono1; clear_ctx; eauto.
    edestruct Hmono2; clear_ctx; eauto.
  - intros f g Hfg a a' Hprec. repeat split; edestruct Hfg; eauto; destruct H2; eauto.
Defined.

Definition sp_fun {A B} `{Refinable A} `{Refinable B} (f : A -> B): (forall a1 a2, a1 ⊑ a2 -> f a1 ⊑ f a2) -> f ⊑ f.
Proof.
  intros; repeat split; eauto.
Qed.

Class Complete (A : Type) `{Refinable A} :=
  {
    is_complete : A -> Prop ;
    is_complete_spec : forall a, is_complete a -> a ⊑ a ;
  }.

Arguments is_complete : simpl never.

#[export, refine] Instance completeFun {A B} `{Complete A} `{Complete B} : Complete (A -> B) :=
  {
    is_complete f := f ⊑ f /\ forall a, is_complete a -> is_complete (f a) ;
    is_complete_spec := _;
  }.
Proof.
  cbn. intros f [Hf Hcompl] a1 a2 ?; eauto.
Defined.

Lemma is_complete_const_fun : forall {A B} `{Complete A} `{Complete B} (b : B), is_complete b -> is_complete (fun _ : A => b).
Proof.  simpl; intros. split.
  - unfold is_refinement; cbn. eapply is_complete_spec in H3; eauto.
  - eauto.
Qed.

#[export] Hint Resolve is_complete_const_fun : typeclass_instances.

Class Ground (A : Type) `{Refinable A} `{Complete A} : Type :=
  {
    is_complete_minimal : forall a, is_complete a -> forall a', a' ⊑ a -> a' = a
  }.


Tactic Notation "unfold_complete" "in" hyp(H) := unfold is_complete in H; cbn in H.
Tactic Notation "unfold_complete" := unfold is_complete; cbn.
Tactic Notation "unfold_refinement" := unfold is_refinement; cbn.
Tactic Notation "unfold_refinement" "in" hyp(H) := unfold is_refinement in H; cbn in H.
  
From Coq Require Import FunctionalExtensionality.

Section Monotonicity.
  Context {A} `{HAC : Complete A}.

  Class Monotonizable (P : A -> Prop) :=
    {
      monotone : A -> Prop;
      antitone : A -> Prop;
      is_monotone : forall a1 a2, a1 ⊑ a2 -> monotone a1 -> monotone a2;
      is_antitone : forall a1 a2, a1 ⊑ a2 -> antitone a2 -> antitone a1;
      complete_monotone_is_equivalent : forall (a : A), is_complete a -> monotone a <-> P a;
      complete_antitone_is_equivalent : forall (a : A), is_complete a -> antitone a <-> P a
    }.

  Definition monotonize (P : A -> Prop) `{Monotonizable P} : A -> Prop := monotone.
  Definition antitonize (P : A -> Prop) `{Monotonizable P} : A -> Prop := antitone.

  Corollary incompleteness_tolerance : forall (P : A -> Prop) {HP: Monotonizable P} (a1 a2 : A),
    is_complete a1 -> a1 ⊑ a2 -> P a1 -> monotone a2.
  Proof.
    intros P HP a1 a2 Hac Hprec HP1.
    eapply HP.(is_monotone); try eapply Hprec; eauto.
    apply HP.(complete_monotone_is_equivalent); eauto.
  Qed.

  #[export] Program Instance monotonizable_const (P : Prop) : Monotonizable (fun a => P) := {
      monotone := fun _ => P ;
      antitone := fun _ => P ;
      is_monotone := ltac:(eauto) ;
      is_antitone := ltac:(eauto) ;
      complete_monotone_is_equivalent := ltac:(now eauto) ;
      complete_antitone_is_equivalent := ltac:(now eauto)
    }.

  #[export] Program Instance monotonizable_eq {B} `{HB : Ground B}
    (g h : A -> B) (Hcg : is_complete g) (Hch : is_complete h)
    : Monotonizable (fun a => g a = h a) | 2
    := {
      monotone := fun a => exists b, b ⊑ g a /\ b ⊑ h a ;
      antitone := fun a => is_complete (g a) /\ g a = h a ; 
      is_monotone := _ ;
      is_antitone := _ ;
      complete_monotone_is_equivalent := _ ;
      complete_antitone_is_equivalent := _
    }.
  Next Obligation.
    intros ? ? ? ? ? g h ? ? a1 a2 Hprec [b [? ?]].
    exists b. split.
    - apply is_transitive with (g a1) ; auto. eapply is_complete_spec in Hcg; edestruct Hcg; eauto.
    - apply is_transitive with (h a1) ; auto. eapply is_complete_spec in Hch; edestruct Hch; eauto.
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
      is_monotone := _ ;
      is_antitone := _ ;
      complete_monotone_is_equivalent := _ ;
      complete_antitone_is_equivalent := _
    }.
  Next Obligation.
    intros ? ? ? ? ? g [Hcg ?] b a1 a2 Hprec ?.
    apply is_transitive with (g a1); try apply Hcg; eauto.
  Qed.
  Next Obligation.
  intros ? ? ? ? ? g [Hcg ?] b a1 a2 Hprec [? ?].
  unfold_refinement in Hcg. edestruct Hcg as [Hmono ?]; eauto. apply is_complete_minimal in Hmono; eauto.
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

  (* #[export] Program Instance monotonizable_eq_3 {B} `{HB : Ground B}
    (g : A -> B) (Hcg : is_complete g) (b : B) : Monotonizable (fun a => b = g a) | 1 := {
      monotone := fun a => b ⊑ g a ;
      antitone := fun a => is_complete b /\ g a ⊑ b ;
      is_monotone := _ ;
      is_antitone := _ ;
      complete_monotone_is_equivalent := _ ;
      complete_antitone_is_equivalent := _
    }.
  Next Obligation.
    intros ? ? ? ? ? g [Hcg ?] b a1 a2 Hprec ?.
    apply is_transitive with (g a1); try apply Hcg; eauto.
  Qed.
  Next Obligation.
  intros ? ? ? ? ? g [Hcg ?] b a1 a2 Hprec [? ?]; split; eauto.
  apply is_transitive with (g a2); try apply Hcg; eauto.
  Qed.
  Next Obligation.
    intros B ? ? ? ? g [? ?] ? a Hca. split; [intros Hbg | intros ->].
    - eapply is_complete_minimal in Hbg; eauto.
    - apply is_complete_spec; eauto.
  Qed.
  Next Obligation.
    intros B ? ? ? ? g [? ?] ? a Hca. split; [intros [? Hbg] | intros ->].
    - eapply is_complete_minimal in Hbg; eauto.
    - split; eauto; apply is_complete_spec; eauto.
  Qed. *)

  #[export] Program Instance monotonizable_eq_fun {B C} `{HB : Refinable B} `{HC : Refinable C}
    (g h : A -> B -> C) {Hmono : Monotonizable (fun a => forall b, g a b = h a b)} : Monotonizable (fun a => g a = h a) := {
      monotone := Hmono.(monotone) ;
      antitone := Hmono.(antitone) ;
      is_monotone := _ ;
      is_antitone := _ ;
      complete_monotone_is_equivalent := _ ;
      complete_antitone_is_equivalent := _
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
      monotone := fun a => forall b, (HPB b).(monotone) a ;
      antitone := fun a => forall b, (HPB b).(antitone) a ;
      is_monotone := _ ;
      is_antitone := _ ;
      complete_monotone_is_equivalent := _ ;
      complete_antitone_is_equivalent := _
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
      monotone := fun a => exists b, (HPB b).(monotone) a ;
      antitone := fun a => exists b, (HPB b).(antitone) a ;
      is_monotone := _ ;
      is_antitone := _ ;
      complete_monotone_is_equivalent := _ ;
      complete_antitone_is_equivalent := _
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
      monotone := fun a => (HP.(monotone) a) /\ (HQ.(monotone) a) ;
      antitone := fun a => (HP.(antitone) a) /\ (HQ.(antitone) a) ;
      is_monotone := _ ;
      is_antitone := _ ;
      complete_monotone_is_equivalent := _ ;
      complete_antitone_is_equivalent := _
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
      monotone := fun a => (HP.(monotone) a) \/ (HQ.(monotone) a) ;
      antitone := fun a => (HP.(antitone) a) \/ (HQ.(antitone) a) ;
      is_monotone := _ ;
      is_antitone := _ ;
      complete_monotone_is_equivalent := _ ;
      complete_antitone_is_equivalent := _
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
      monotone := fun a => HP.(antitone) a -> HQ.(monotone) a ;
      antitone := fun a => HP.(monotone) a -> HQ.(antitone) a ;
      is_monotone := _ ;
      is_antitone := _ ;
      complete_monotone_is_equivalent := _ ;
      complete_antitone_is_equivalent := _
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
      is_monotone := _ ;
      is_antitone := _ ;
      complete_monotone_is_equivalent := _ ;
      complete_antitone_is_equivalent := _
    }.
  Next Obligation.
    intros ? ? ? ? ? g ? b ? a1 a2 Hprec ?.
    apply is_transitive with (g a1); eauto.
    apply Hcg; eauto.
  Qed.
  Next Obligation.
    intros ? ? ? ? ? g ? b ? a1 a2 Hprec ?.
    apply is_transitive with (g a2); eauto.
    apply Hcg; eauto.
  Qed.
  Next Obligation.
    intros B ? ? ? ? g ? ? ? a Hca.
    split; intros Hbg; pose proof (Hbg' := Hbg); eapply is_complete_minimal in Hbg; eauto; try rewrite Hbg.
    - eapply is_right_reflexive; eauto.
    - apply Hcg; eauto.
    - eapply is_right_reflexive; eauto.
  Qed.
  Next Obligation.
    intros B ? ? ? ? g ? ? ? a Hca; split; eauto.
  Qed.

End Monotonicity.


#[export] Hint Extern 0 (Complete _) => eassumption : typeclass_instances.

Lemma fun_is_complete_if_complete_dom : forall {A B} `{Complete A} `{Complete B},
    forall a, is_complete a -> is_complete (fun f : A -> B => f a).
Proof.
  simpl; intros; split.
  - unfold is_refinement; cbn. intros. edestruct H4; eauto. eapply is_complete_spec in H3; eauto.
  - intros. destruct H4. eauto.
Qed.

#[export] Hint Resolve fun_is_complete_if_complete_dom : typeclass_instances.
