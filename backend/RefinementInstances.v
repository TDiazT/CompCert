Require Import Coq.Relations.Relation_Definitions.
Require Export Refinement.
Require Import FunInd.
Require Import Coqlib Maps Errors Integers Floats Lattice Kildall.
Require Import AST Linking.
Require Import Values Memory Globalenvs Events Smallstep.
Require Import Registers Op RTL RTL_Incomplete.
Require Import ValueDomain ValueAnalysis NeedDomain NeedOp.

(* Destructs conjunctions, disjunctions, etc. *)
Ltac destruct_ctx := 
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
  end
  ).


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

Lemma reflRefinableEq {A} (HRA := mkEqRefinable A) : forall a : A, a ⊑ a.
Proof. reflexivity. Qed.

Hint Resolve reflRefinableEq : core.

Lemma completeTrue {A} (HRA := mkEqRefinable A) (HCA := mkCompleteTrue A) : forall a : A, is_complete a.
Proof. compute; eauto. Qed.
  
Hint Resolve completeTrue : core.

#[export, refine] Instance refinableRes {A} `{Refinable A} : Refinable (res A) := 
{
  refinement r1 r2 := match r1, r2 with 
  | OK x1, OK x2 => x1 ⊑ x2
  (* Just to get ground *)
  | Error e1, Error e2 => e1 = e2
  | _, _ => False
  end
}.
Proof.
  - unfold Relation_Definitions.transitive; intros [] [] [] ? ?; eauto; try contradiction.
    * eapply is_transitive; eauto.
    * subst; eauto.
  - intros [] []; eauto; try eapply is_right_reflexive; eauto; try contradiction.
Defined.

#[export, refine] Instance completeRes {A} `{Complete A} : Complete (res A) := 
  {
    is_complete := fun r => match r with
    | OK x => is_complete x
    | Error _ => True
    end
  }.
Proof.
  intros []; eauto; intros; simpl; eauto; unfold refinement; cbn; try apply is_complete_spec; eauto.
Defined.

#[export] Instance groundRes {A} `{Ground A} : Ground (res A).
Proof. constructor; intros [] ? []; simpl; try contradiction; intros.
      - f_equal. eapply is_complete_minimal; eauto.
      - unfold refinement in H4; cbn in H4; subst; eauto.
Defined. 

#[export, refine] Instance refinableOption {A} `{Refinable A} : Refinable (option A) := 
{
  refinement o1 o2 := match o1, o2 with 
  | Some x1, Some x2 => x1 ⊑ x2
  | None, None => True
  | _, _ => False
  end
}.
Proof.
  - unfold Relation_Definitions.transitive; intros [] [] [] ? ?; eauto; try contradiction.
    eapply is_transitive; eauto.
  - intros [] []; eauto; try eapply is_right_reflexive; eauto; try contradiction.
Defined.

#[export, refine] Instance completeOption {A} `{Complete A} : Complete (option A) := 
  {
    is_complete := fun o => match o with
    | Some x => is_complete x
    | None => True
    end
  }.
Proof.
  intros []; eauto; intros; simpl; eauto. unfold refinement; cbn; apply is_complete_spec; eauto.
Defined.

#[export] Instance groundOption {A} `{Ground A} : Ground (option A).
Proof. constructor; intros [] ? []; simpl; try contradiction; intros; eauto.
      f_equal. eapply is_complete_minimal; eauto.
Defined. 

#[export, refine] Instance refinableList {A} `{Refinable A} : Refinable (list A) := 
{
  refinement l1 l2 := let fix aux l1 l2 :=
   match l1, l2 with
    | nil, nil => True
    | x :: xs, y :: ys => x ⊑ y /\ aux xs ys
    | _, _ => False
    end in aux l1 l2
}.
Proof.
  - unfold Relation_Definitions.transitive. induction x; intros; destruct y; eauto; try contradiction.
    destruct z; eauto; try contradiction. destruct H0; destruct H1; split; try eapply is_transitive; eauto.
    eapply IHx; eauto.
  - intros l1; induction l1; intros []; eauto; try contradiction; simpl. intros []; split; try eapply is_right_reflexive; eauto. 
  apply IHl1; eauto.
Defined.

#[export, refine] Instance completeList {A} `{Complete A} : Complete (list A) := 
  {
    is_complete l := let fix aux l := 
    match l with 
    | nil => True 
    | x :: xs => is_complete x /\ aux xs
    end in aux l
  }.
Proof.
  intros l; induction l; eauto. simpl; intros []; constructor; try eapply is_complete_spec; eauto.
  apply IHl; eauto.
Defined.

#[export] Instance groundList {A} `{Ground A} : Ground (list A).
Proof. constructor; intros l; induction l; intros [] []; try contradiction; eauto.
  intros []. f_equal. eapply is_complete_minimal; eauto.
  apply IHl; eauto.
Defined.
  
#[export, refine] Instance refinableSum {A B} `{Refinable A} `{Refinable B} : Refinable (A + B) := 
{
  refinement s1 s2 := match s1, s2 with 
  | inl x1, inl x2 => x1 ⊑ x2
  | inr y1, inr y2 => y1 ⊑ y2
  | _, _ => False
  end
}.
Proof.
  - unfold Relation_Definitions.transitive; intros [] [] [] ? ?; eauto; try contradiction; eapply is_transitive; eauto.
  - intros [] []; eauto; try eapply is_right_reflexive; eauto; try contradiction.
Defined.

#[export, refine] Instance completeSum {A B} `{Complete A} `{Complete B} : Complete (A + B) := 
  {
    is_complete := fun s => match s with
    | inl x => is_complete x
    | inr y => is_complete y
    end
  }.
Proof.
  intros []; eauto; intros; simpl; eauto; unfold_refinement; eapply is_complete_spec; eauto.
Defined.

#[export] Instance groundSum {A B} `{Ground A} `{Ground B} : Ground (A + B).
Proof. constructor; intros [] ? []; simpl; try contradiction; intros; eauto; f_equal; eapply is_complete_minimal; eauto.
Defined.

#[export, refine] Instance refinableProd {A B} `{Refinable A} `{Refinable B} : Refinable (A * B) := 
{
  refinement p1 p2 := let (x1, y1) := p1 in let (x2, y2) := p2 in x1 ⊑ x2 /\ y1 ⊑ y2
}.
Proof.
  - unfold Relation_Definitions.transitive; intros [] [] [] [] []; split; try eapply is_transitive; eauto.
  - intros [] [] []; split; try eapply is_right_reflexive; eauto.
Defined.

#[export, refine] Instance completeProd {A B} `{Complete A} `{Complete B} : Complete (A * B) := 
  {
    is_complete := fun p => let (x, y) := p in is_complete x /\ is_complete y
  }.
Proof.
  intros [] []; constructor; try eapply is_complete_spec; eauto.
Defined.

#[export] Instance groundProd {A B} `{Ground A} `{Ground B} : Ground (A * B).
Proof. constructor; intros [] [] [] []; f_equal; eapply is_complete_minimal; eauto. 
Defined. 

Arguments monotone {A} {H} {HAC} P {Monotonizable}.
#[export, refine] Instance monoForall2 {A B C} `{Complete C} (l1 : list A) (l2 : list B) (f : C -> A -> B -> Prop) {Hf : forall a b, Monotonizable (fun c => f c a b)} : Monotonizable (fun c => list_forall2 (f c) l1 l2) := 
{
  monotone := fun c => list_forall2 (fun a b => (Hf a b).(monotone (fun c => f c a b)) c) l1 l2;
  antitone := fun c => list_forall2 (fun a b => (Hf a b).(antitone) c) l1 l2;
}.
Proof.
  - intros ? ? ?; induction 1; constructor; eauto. eapply is_monotone; eauto.
  - intros ? ? ?; induction 1; constructor; eauto. eapply is_antitone; eauto.
  - intros c ?; split; induction 1; econstructor; eauto.
    * eapply (Hf a1 b1).(complete_monotone_is_equivalent); eauto.
    * eapply (Hf a1 b1).(complete_monotone_is_equivalent); eauto.
  - intros c ?; split; induction 1; econstructor; eauto; eapply (Hf a1 b1).(complete_antitone_is_equivalent); eauto.
Defined.
  
(* node and reg are positive *)
#[export] Instance : Refinable reg := mkEqRefinable reg.
#[export] Instance : Complete reg := mkCompleteTrue reg. 

#[export] Instance : Refinable operation := mkEqRefinable operation.
#[export] Instance : Complete operation := mkCompleteTrue operation.

#[export] Instance : Refinable memory_chunk := mkEqRefinable memory_chunk.
#[export] Instance : Complete memory_chunk := mkCompleteTrue memory_chunk.

#[export] Instance : Refinable addressing := mkEqRefinable addressing. 
#[export] Instance : Complete addressing := mkCompleteTrue addressing.

(* Signature is actually a record *)
#[export] Instance : Refinable signature := mkEqRefinable signature.
#[export] Instance : Complete signature := mkCompleteTrue signature.

(* external_function is an inductive *)
#[export] Instance : Refinable external_function := mkEqRefinable external_function.
#[export] Instance : Complete external_function := mkCompleteTrue external_function.

#[export] Instance : Refinable condition := mkEqRefinable condition.
#[export] Instance : Complete condition := mkCompleteTrue condition.

(* builtin_arg and res are parameterized, so one could have a more general definition *)
#[export] Instance : Refinable (builtin_arg reg) := mkEqRefinable (builtin_arg reg).
#[export] Instance : Complete (builtin_arg reg) := mkCompleteTrue (builtin_arg reg).

#[export] Instance : Refinable (builtin_res reg) := mkEqRefinable (builtin_res reg).
#[export] Instance : Complete (builtin_res reg) := mkCompleteTrue (builtin_res reg).

#[export] Instance : Refinable ablock := mkEqRefinable ablock.
#[export] Instance : Complete ablock := mkCompleteTrue ablock.

#[export] Instance : Refinable Z := mkEqRefinable Z.
#[export] Instance : Complete Z := mkCompleteTrue Z . 

#[export] Instance : Refinable init_data := mkEqRefinable init_data.
#[export] Instance : Complete init_data := mkCompleteTrue init_data.

#[export] Instance : Refinable bool := mkEqRefinable bool.
#[export] Instance : Complete bool := mkCompleteTrue bool.

#[export] Instance : Refinable ident := mkEqRefinable ident.

#[export] Instance : Refinable unit := mkEqRefinable unit.
#[export] Instance : Complete unit := mkCompleteTrue unit.

#[export] Instance : Refinable val := mkEqRefinable val.
#[export] Instance : Complete val := mkCompleteTrue val.

#[export] Instance : Refinable mem := mkEqRefinable mem.
#[export] Instance : Complete mem := mkCompleteTrue mem.

#[export] Instance : Refinable RTL.instruction := mkEqRefinable RTL.instruction.
#[export] Instance : Complete RTL.instruction := mkCompleteTrue RTL.instruction.

#[local] Obligation Tactic := idtac.

Definition refinement_instruction : relation instruction  := fun i1 i2 =>
match i1, i2 with
| Inop n1, Inop n2 => n1 ⊑ n2
| Iop op1 args1 res1 n1, Iop op2 args2 res2 n2 => op1 ⊑ op2 /\ args1 ⊑ args2 /\ res1 ⊑ res2 /\ n1 ⊑ n2
| Iload chunk1 addr1 args1 res1 n1, Iload chunk2 addr2 args2 res2 n2 => chunk1 ⊑ chunk2 /\ addr1 ⊑ addr2 /\ args1 ⊑ args2 /\ res1 ⊑ res2 /\ n1 ⊑ n2
| Istore chunk1 addr1 args1 args1' n1, Istore chunk2 addr2 args2 args2' n2 => chunk1 ⊑ chunk2 /\ addr1 ⊑ addr2 /\ args1 ⊑ args2 /\ args1' ⊑ args2' /\ n1 ⊑ n2
| Icall sig1 ros1 args1 res1 n1, Icall sig2 ros2 args2 res2 n2 => sig1 ⊑ sig2 /\ ros1 ⊑ ros2 /\ args1 ⊑ args2 /\ res1 ⊑ res2 /\ n1 ⊑ n2
| Itailcall sig1 ros1 args1, Itailcall sig2 ros2 args2 => sig1 ⊑ sig2 /\ ros1 ⊑ ros2 /\ args1 ⊑ args2
| Ibuiltin ef1 args1 res1 n1, Ibuiltin ef2 args2 res2 n2 => ef1 ⊑ ef2 /\ args1 ⊑ args2 /\ res1 ⊑ res2 /\ n1 ⊑ n2
| Icond cond1 args1 n11 n12, Icond cond2 args2 n21 n22 => cond1 ⊑ cond2 /\ args1 ⊑ args2 /\ n11 ⊑ n21 /\ n12 ⊑ n22
| Ijumptable r1 n1, Ijumptable r2 n2 => r1 ⊑ r2 /\ n1 ⊑ n2
| Ireturn mr1, Ireturn mr2 => mr1 ⊑ mr2
| _ , Inotimplemented => True
| _ , _ => False
end.

#[export] Program Instance refinableInstruction : Refinable instruction :=
  {|
    refinement i1 i2 := refinement_instruction i1 i2
  |}.
  Next Obligation. 
    red; intros [] [] []; intros H H0; cbn in *; eauto.
    all: try solve [inversion H]; try solve [inversion H0].
    all: destruct_ctx; repeat split; etransitivity; eauto.
  Qed. 
  Next Obligation.
    intros [] [] H; cbn in *; eauto. 
    all: try solve [inversion H].
    all: destruct_ctx; repeat split; eapply is_right_reflexive; eauto.
  Qed. 
  
Inductive is_complete_instruction : instruction -> Prop :=
| is_complete_Inop : forall n, is_complete n -> is_complete_instruction (Inop n)
| is_complete_Iop : forall op args res n, is_complete op -> is_complete args -> is_complete res -> is_complete n -> is_complete_instruction (Iop op args res n)
| is_complete_Iload : forall chunk addr args res n, is_complete chunk -> is_complete addr -> is_complete args -> is_complete res -> is_complete n -> is_complete_instruction (Iload chunk addr args res n)
| is_complete_Istore : forall chunk addr args args' n, is_complete chunk -> is_complete addr -> is_complete args -> is_complete args' -> is_complete n -> is_complete_instruction (Istore chunk addr args args' n)
| is_complete_Icall : forall sig ros args res n, is_complete sig -> is_complete ros -> is_complete args -> is_complete res -> is_complete n -> is_complete_instruction (Icall sig ros args res n)
| is_complete_Itailcall : forall sig ros args, is_complete sig -> is_complete ros -> is_complete args -> is_complete_instruction (Itailcall sig ros args)
| is_complete_Ibuiltin : forall ef args res n, is_complete ef -> is_complete args -> is_complete res -> is_complete n -> is_complete_instruction (Ibuiltin ef args res n)
| is_complete_Icond : forall cond args n1 n2, is_complete cond -> is_complete args -> is_complete n1 -> is_complete n2 -> is_complete_instruction (Icond cond args n1 n2)
| is_complete_Ijumptable : forall r n, is_complete r -> is_complete n -> is_complete_instruction (Ijumptable r n)
| is_complete_Ireturn : forall mr, is_complete mr -> is_complete_instruction (Ireturn mr).

#[export] Program Instance completeInstruction : Complete instruction := 
{ 
  is_complete := is_complete_instruction
}.
Next Obligation.
  intros []; inversion 1; cbn in *; red; cbn. 
  all: destruct_ctx; repeat split; eapply is_complete_spec; eauto.
Qed. 


#[export, refine ] Instance groundInstruction : Ground instruction := {}. 
Proof.
  intros []; inversion 1; intros [] Href; red in Href; cbn in *.
  all: try solve [inversion Href].
  all: destruct_ctx; f_equal; eauto.
  all: eapply is_complete_minimal; eauto.
 Qed.  

#[export] Program Instance refinablePTree {A} `{Refinable A} : Refinable (PTree.t A) := 
{
  refinement t1 t2 := forall pc, t1 ! pc ⊑ t2 ! pc  
}.
Next Obligation.
  red; intros. etransitivity; eauto.
Qed.    
Next Obligation.
  cbn; intros. eapply is_right_reflexive; eauto.
Qed.    

#[export] Program Instance completePTree {A} `{Complete A} : Complete (PTree.t A) := 
{
  is_complete t := forall pc, is_complete (t ! pc)
}.
Next Obligation.
  cbn; intros; red; cbn. intro. eapply is_complete_spec; eauto.
Qed.

(*
#[export] Program Instance groundPTree {A} `{Ground A} : Ground (PTree.t A) := 
{
  is_complete_minimal := _
}.
Next Obligation.
(*   cbn; intros; cbn. eapply is_complete_minimal; eauto.
  Unshelve. 
 *)
Admitted.
*)

#[export] Instance : Refinable romem. apply refinablePTree. Defined.
#[export] Instance : Complete romem. apply completePTree. Defined.
Lemma romem_complete : forall r : romem, is_complete r. 
Proof. intros; unfold_complete; intros; unfold_complete; destruct (_ ! _); try unfold_complete; eauto. Qed.
Lemma romem_sp : forall r : romem, r ⊑ r. 
Proof. intros; unfold_refinement; intros; unfold_refinement; destruct (_ ! _); try unfold_refinement; eauto. Qed.


#[export] Instance : Refinable RTL.function := mkEqRefinable RTL.function.
#[export] Instance : Complete RTL.function := mkCompleteTrue RTL.function.

#[export, refine] Instance : Refinable function := 
  {
    refinement f1 f2 := 
    (fn_sig f1) ⊑ (fn_sig f2) /\ (fn_params f1) ⊑ (fn_params f2) /\ (fn_stacksize f1) ⊑ (fn_stacksize f2) /\ (fn_code f1) ⊑ (fn_code f2) /\ (fn_entrypoint f1) ⊑ (fn_entrypoint f2)
  }.
Proof. 
  - unfold Relation_Definitions.transitive; intros [] [] [] ? ?.
    destruct_ctx.
    repeat split; try eapply is_transitive; eauto.
  - intros [] [] ?; destruct_ctx. repeat split; try eapply is_right_reflexive; eauto.
Defined.


#[export] Program Instance : Complete function := {
  is_complete f := 
  is_complete (fn_sig f) /\ is_complete (fn_params f) /\ is_complete (fn_stacksize f) /\ is_complete (fn_code f) /\ is_complete (fn_entrypoint f)
  (* forall pc, is_complete pc -> is_complete ((fn_code f) ! pc) *)
}.
Next Obligation.
  cbn; intros. destruct_ctx. red; cbn. repeat split; eauto; eapply is_complete_spec; eauto.
Qed. 

(*
#[export] Instance : Ground function.
Proof. constructor. intros [] HC [] HR. unfold_complete in HC; unfold_refinement in HR. destruct_ctx. unshelve f_equal; unshelve eapply is_complete_minimal; eauto; try typeclasses eauto.
Defined.
*)

(*

#[export] Program Instance refinableGlobvar {V} `{Refinable V} : Refinable (globvar V) := 
{
  refinement g1 g2 := (gvar_info g1) ⊑ (gvar_info g2) /\ (gvar_init g1) ⊑ (gvar_init g2) /\ (gvar_readonly g1) ⊑ (gvar_readonly g2) /\ (gvar_volatile g1) ⊑ (gvar_volatile g2)
}.
Next Obligation. 
Admit Obligations.

#[export] Program Instance completeGlobvar {V} `{Complete V} : Complete (globvar V) := 
{
  is_complete g := is_complete (gvar_info g) /\ is_complete (gvar_init g) /\ is_complete (gvar_readonly g) /\ is_complete (gvar_volatile g)
}.
Admit Obligations.

Inductive refinement_globdef {F V} `{Refinable F} `{Refinable V} : globdef F V -> globdef F V -> Prop :=
| refinement_Gfun : forall f1 f2, f1 ⊑ f2 -> refinement_globdef (Gfun f1) (Gfun f2)
| refinement_Gvar : forall v1 v2, v1 ⊑ v2 -> refinement_globdef (Gvar v1) (Gvar v2).

#[export] Program Instance refinableGlobdef {F V} `{Refinable F} `{Refinable V} : Refinable (globdef F V) := 
{
  refinement := refinement_globdef
}.
Admit Obligations.

Inductive is_complete_globdef {F V} `{Complete F} `{Complete V} : globdef F V -> Prop :=
| is_complete_Gfun : forall f, is_complete f -> is_complete_globdef (Gfun f)
| is_complete_Gvar : forall v, is_complete v -> is_complete_globdef (Gvar v).

#[export] Program Instance completeGlobdef {F V} `{Complete F} `{Complete V} : Complete (globdef F V) := 
{
  is_complete := is_complete_globdef
}.
Admit Obligations.
*)

Definition refinementFunDef {F} `{Refinable F} : relation (AST.fundef F) := fun fd1 fd2 =>
  match fd1, fd2 with
  | External ef1, External ef2 => ef1 ⊑ ef2
  | Internal f1, Internal f2 => f1 ⊑ f2
  | _, _ => False
  end.

#[export] Program Instance refinableASTFundef {F} `{Refinable F} : Refinable (AST.fundef F) := 
{
  refinement := refinementFunDef 
}.
Next Obligation.
  red; cbn; intros ? ? [] [] []; cbn; eauto. 
  all: try inversion 1; try inversion 2.
  all: try etransitivity; eauto.
Qed. 
Next Obligation.
  red; cbn; intros ? ? [] []; cbn; eauto. 
  all: try inversion 1; try inversion 2.
  eapply is_right_reflexive; eauto.
Qed. 

#[export] Program Instance completeASTFundef {F} `{Complete F} : Complete (AST.fundef F) := 
{
  is_complete fd := 
    match fd with
    | External ef => is_complete ef
    | Internal f => is_complete f
    end
}.
Next Obligation.
  red; cbn; intros ? ? [] []; cbn; eauto. 
Qed. 

(*
#[export] Instance groundASTFundef {F} `{Ground F} : Ground (AST.fundef F).
Proof. constructor. intros [] ? [] ?; try contradiction;
  try f_equal; eauto; eapply is_complete_minimal; eauto.
Qed.
*)

#[export] Instance : Refinable fundef. apply refinableASTFundef. Defined.
#[export] Instance : Complete fundef. apply completeASTFundef. Defined.
(* #[export] Instance : Ground fundef. Admitted. *)

#[export] Instance : Refinable RTL.program := mkEqRefinable RTL.program.
#[export] Instance : Complete RTL.program := mkCompleteTrue RTL.program.

#[export] Program Instance refinableASTProgram : Refinable program := 
{
  refinement p1 p2 := forall ros rs, find_function (Genv.globalenv p1) ros rs ⊑ find_function (Genv.globalenv p2) ros rs
}.
Next Obligation.
  red; cbn; intros. etransitivity; eauto.
Qed. 
Next Obligation.
  cbn; intros. eapply is_right_reflexive; eauto.
Qed. 

#[export] Program Instance completeASTProgram : Complete program := 
{
  is_complete p := (forall ros rs, is_complete (find_function (Genv.globalenv p) ros rs)) /\ forall b, is_complete (Genv.find_funct_ptr (Genv.globalenv p) b)
}.
Next Obligation.
  red; cbn; intros. destruct_ctx. eapply is_complete_spec; eauto.
Qed. 

#[export] Instance : Refinable program. apply refinableASTProgram. Defined.
#[export] Instance : Complete program. apply completeASTProgram. Defined.

#[export] Instance : Refinable code. apply refinablePTree. Defined.
#[export] Instance : Complete code. apply completePTree. Defined.
(* #[export] Instance : Ground code. apply groundPTree. Defined.
 *)
#[export] Instance : Refinable code. apply refinablePTree. Defined.
#[export] Instance : Complete code. apply completePTree. Defined.
(* #[export] Instance : Ground code. apply groundPTree. Defined.
 *)

#[export, refine] Instance : Refinable stackframe := 
{
  refinement '(Stackframe r1 f1 v1 n1 rs1) '(Stackframe r2 f2 v2 n2 rs2) := 
  r1 ⊑ r2 /\ f1 ⊑ f2 /\ v1 ⊑ v2 /\ n1 ⊑ n2 /\ rs1 ⊑ rs2
}.
Proof.
  - unfold Relation_Definitions.transitive; intros [] [] [] ? ?; destruct_ctx.
    unfold_refinement in H7; unfold_refinement in H0; destruct_ctx. 
    repeat split; eapply is_transitive; eauto.
  - intros [] [] ?; destruct_ctx. unfold_refinement in H2; destruct_ctx.
    repeat split; try eapply is_right_reflexive; eauto.
Defined.

Inductive refinement_state : state -> state -> Prop :=
| refinement_State : forall sfr1 sfr2 f1 f2 v1 v2 n1 n2 r1 r2 m1 m2, 
  sfr1 ⊑ sfr2 -> f1 ⊑ f2 -> v1 ⊑ v2 -> n1 ⊑ n2 -> r1 ⊑ r2 -> m1 ⊑ m2 -> refinement_state (State sfr1 f1 v1 n1 r1 m1) (State sfr2 f2 v2 n2 r2 m2)
| refinement_Callstate : forall sfr1 sfr2 fd1 fd2 v1 v2 m1 m2,
  sfr1 ⊑ sfr2 -> fd1 ⊑ fd2 -> v1 ⊑ v2 -> m1 ⊑ m2 -> refinement_state (Callstate sfr1 fd1 v1 m1) (Callstate sfr2 fd2 v2 m2)
| refinement_Returnstate : forall sfr1 sfr2 v1 v2 m1 m2, 
  sfr1 ⊑ sfr2 -> v1 ⊑ v2 -> m1 ⊑ m2 -> refinement_state (Returnstate sfr1 v1 m1) (Returnstate sfr2 v2 m2).

#[export] Program Instance : Refinable state := 
{
  refinement := refinement_state
}.
Next Obligation.
  intros ? ? ? []; inversion 1; constructor; etransitivity; eauto.
Qed. 
Next Obligation.
  intros ? ? []; constructor; eapply is_right_reflexive; eauto.
Qed.