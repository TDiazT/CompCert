(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Elimination of unneeded computations over RTL: correctness proof. *)
Require Import RefinementInstances.

Require Import FunInd.
Require Import Coqlib Maps Errors Integers Floats Lattice Kildall.
Require Import AST Linking.
Require Import Values Memory Globalenvs Events Smallstep.
Require Import Registers Op RTL_Incomplete RTL.
Require Import ValueDomain ValueAnalysis NeedDomain NeedOp Deadcode.



Lemma function_complete : forall f : function, is_complete f.
easy.
Qed.

Hint Resolve function_complete.

(* Beginning of the file *)

(* Definition match_prog_aux trans_f (prog : program) (tprog: RTL_Incomplete.program) := *)
(* match_program (fun cu f tf => transf_fundef_aux trans_f (romem_for cu) f = OK tf) eq prog tprog. *)
Definition match_prog_aux {A B} transf_f (prog : @program_ A) (tprog: @program_ B) := 
  match_program (fun cu f tf => AST.transf_partial_fundef (transf_f (romem_for cu)) f = OK tf) eq prog tprog.


(** * Relating the memory states *)

(** The [magree] predicate is a variant of [Mem.extends] where we
  allow the contents of the two memory states to differ arbitrarily
  on some locations.  The predicate [P] is true on the locations whose
  contents must be in the [lessdef] relation. *)

Definition locset := block -> Z -> Prop.

Record magree (m1 m2: mem) (P: locset) : Prop := mk_magree {
  ma_perm:
    forall b ofs k p,
    Mem.perm m1 b ofs k p -> Mem.perm m2 b ofs k p;
  ma_perm_inv:
    forall b ofs k p,
    Mem.perm m2 b ofs k p -> Mem.perm m1 b ofs k p \/ ~Mem.perm m1 b ofs Max Nonempty;
  ma_memval:
    forall b ofs,
    Mem.perm m1 b ofs Cur Readable ->
    P b ofs ->
    memval_lessdef (ZMap.get ofs (PMap.get b (Mem.mem_contents m1)))
                   (ZMap.get ofs (PMap.get b (Mem.mem_contents m2)));
  ma_nextblock:
    Mem.nextblock m2 = Mem.nextblock m1
}.

Lemma magree_monotone:
  forall m1 m2 (P Q: locset),
  magree m1 m2 P ->
  (forall b ofs, Q b ofs -> P b ofs) ->
  magree m1 m2 Q.
Proof.
  intros. destruct H. constructor; auto.
Qed.

Lemma mextends_agree:
  forall m1 m2 P, Mem.extends m1 m2 -> magree m1 m2 P.
Proof.
  intros. destruct H. destruct mext_inj. constructor; intros.
- replace ofs with (ofs + 0) by lia. eapply mi_perm; eauto. auto.
- eauto.
- exploit mi_memval; eauto. unfold inject_id; eauto.
  rewrite Z.add_0_r. auto.
- auto.
Qed.

Lemma magree_extends:
  forall m1 m2 (P: locset),
  (forall b ofs, P b ofs) ->
  magree m1 m2 P -> Mem.extends m1 m2.
Proof.
  intros. destruct H0. constructor; auto. constructor; unfold inject_id; intros.
- inv H0. rewrite Z.add_0_r. eauto.
- inv H0. apply Z.divide_0_r.
- inv H0. rewrite Z.add_0_r. eapply ma_memval0; eauto.
Qed.

Lemma magree_loadbytes:
  forall m1 m2 P b ofs n bytes,
  magree m1 m2 P ->
  Mem.loadbytes m1 b ofs n = Some bytes ->
  (forall i, ofs <= i < ofs + n -> P b i) ->
  exists bytes', Mem.loadbytes m2 b ofs n = Some bytes' /\ list_forall2 memval_lessdef bytes bytes'.
Proof.
  assert (GETN: forall c1 c2 n ofs,
    (forall i, ofs <= i < ofs + Z.of_nat n -> memval_lessdef (ZMap.get i c1) (ZMap.get i c2)) ->
    list_forall2 memval_lessdef (Mem.getN n ofs c1) (Mem.getN n ofs c2)).
  {
    induction n; intros; simpl.
    constructor.
    rewrite Nat2Z.inj_succ in H. constructor.
    apply H. lia.
    apply IHn. intros; apply H; lia.
  }
Local Transparent Mem.loadbytes.
  unfold Mem.loadbytes; intros. destruct H.
  destruct (Mem.range_perm_dec m1 b ofs (ofs + n) Cur Readable); inv H0.
  rewrite pred_dec_true. econstructor; split; eauto.
  apply GETN. intros. rewrite Z_to_nat_max in H.
  assert (ofs <= i < ofs + n) by extlia.
  apply ma_memval0; auto.
  red; intros; eauto.
Qed.

Lemma magree_load:
  forall m1 m2 P chunk b ofs v,
  magree m1 m2 P ->
  Mem.load chunk m1 b ofs = Some v ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> P b i) ->
  exists v', Mem.load chunk m2 b ofs = Some v' /\ Val.lessdef v v'.
Proof.
  intros. exploit Mem.load_valid_access; eauto. intros [A B].
  exploit Mem.load_loadbytes; eauto. intros [bytes [C D]].
  exploit magree_loadbytes; eauto. intros [bytes' [E F]].
  exists (decode_val chunk bytes'); split.
  apply Mem.loadbytes_load; auto.
  apply val_inject_id. subst v. apply decode_val_inject; auto.
Qed.

Lemma magree_storebytes_parallel:
  forall m1 m2 (P Q: locset) b ofs bytes1 m1' bytes2,
  magree m1 m2 P ->
  Mem.storebytes m1 b ofs bytes1 = Some m1' ->
  (forall b' i, Q b' i ->
                b' <> b \/ i < ofs \/ ofs + Z.of_nat (length bytes1) <= i ->
                P b' i) ->
  list_forall2 memval_lessdef bytes1 bytes2 ->
  exists m2', Mem.storebytes m2 b ofs bytes2 = Some m2' /\ magree m1' m2' Q.
Proof.
  assert (SETN: forall (access: Z -> Prop) bytes1 bytes2,
    list_forall2 memval_lessdef bytes1 bytes2 ->
    forall p c1 c2,
    (forall i, access i -> i < p \/ p + Z.of_nat (length bytes1) <= i -> memval_lessdef (ZMap.get i c1) (ZMap.get i c2)) ->
    forall q, access q ->
    memval_lessdef (ZMap.get q (Mem.setN bytes1 p c1))
                   (ZMap.get q (Mem.setN bytes2 p c2))).
  {
    induction 1; intros; simpl.
  - apply H; auto. simpl. lia.
  - simpl length in H1; rewrite Nat2Z.inj_succ in H1.
    apply IHlist_forall2; auto.
    intros. rewrite ! ZMap.gsspec. destruct (ZIndexed.eq i p). auto.
    apply H1; auto. unfold ZIndexed.t in *; lia.
  }
  intros.
  destruct (Mem.range_perm_storebytes m2 b ofs bytes2) as [m2' ST2].
  { erewrite <- list_forall2_length by eauto. red; intros.
    eapply ma_perm; eauto.
    eapply Mem.storebytes_range_perm; eauto. }
  exists m2'; split; auto.
  constructor; intros.
- eapply Mem.perm_storebytes_1; eauto. eapply ma_perm; eauto.
  eapply Mem.perm_storebytes_2; eauto.
- exploit ma_perm_inv; eauto using Mem.perm_storebytes_2.
  intuition eauto using Mem.perm_storebytes_1, Mem.perm_storebytes_2.
- rewrite (Mem.storebytes_mem_contents _ _ _ _ _ H0).
  rewrite (Mem.storebytes_mem_contents _ _ _ _ _ ST2).
  rewrite ! PMap.gsspec. destruct (peq b0 b).
+ subst b0. apply SETN with (access := fun ofs => Mem.perm m1' b ofs Cur Readable /\ Q b ofs); auto.
  intros. destruct H5. eapply ma_memval; eauto.
  eapply Mem.perm_storebytes_2; eauto.
+ eapply ma_memval; eauto. eapply Mem.perm_storebytes_2; eauto.
- rewrite (Mem.nextblock_storebytes _ _ _ _ _ H0).
  rewrite (Mem.nextblock_storebytes _ _ _ _ _ ST2).
  eapply ma_nextblock; eauto.
Qed.

Lemma magree_store_parallel:
  forall m1 m2 (P Q: locset) chunk b ofs v1 m1' v2,
  magree m1 m2 P ->
  Mem.store chunk m1 b ofs v1 = Some m1' ->
  vagree v1 v2 (store_argument chunk) ->
  (forall b' i, Q b' i ->
                b' <> b \/ i < ofs \/ ofs + size_chunk chunk <= i ->
                P b' i) ->
  exists m2', Mem.store chunk m2 b ofs v2 = Some m2' /\ magree m1' m2' Q.
Proof.
  intros.
  exploit Mem.store_valid_access_3; eauto. intros [A B].
  exploit Mem.store_storebytes; eauto. intros SB1.
  exploit magree_storebytes_parallel. eauto. eauto.
  instantiate (1 := Q). intros. rewrite encode_val_length in H4.
  rewrite <- size_chunk_conv in H4. apply H2; auto.
  eapply store_argument_sound; eauto.
  intros [m2' [SB2 AG]].
  exists m2'; split; auto.
  apply Mem.storebytes_store; auto.
Qed.

Lemma magree_storebytes_left:
  forall m1 m2 P b ofs bytes1 m1',
  magree m1 m2 P ->
  Mem.storebytes m1 b ofs bytes1 = Some m1' ->
  (forall i, ofs <= i < ofs + Z.of_nat (length bytes1) -> ~(P b i)) ->
  magree m1' m2 P.
Proof.
  intros. constructor; intros.
- eapply ma_perm; eauto. eapply Mem.perm_storebytes_2; eauto.
- exploit ma_perm_inv; eauto.
  intuition eauto using Mem.perm_storebytes_1, Mem.perm_storebytes_2.
- rewrite (Mem.storebytes_mem_contents _ _ _ _ _ H0).
  rewrite PMap.gsspec. destruct (peq b0 b).
+ subst b0. rewrite Mem.setN_outside. eapply ma_memval; eauto. eapply Mem.perm_storebytes_2; eauto.
  destruct (zlt ofs0 ofs); auto. destruct (zle (ofs + Z.of_nat (length bytes1)) ofs0); try lia.
  elim (H1 ofs0). lia. auto.
+ eapply ma_memval; eauto. eapply Mem.perm_storebytes_2; eauto.
- rewrite (Mem.nextblock_storebytes _ _ _ _ _ H0).
  eapply ma_nextblock; eauto.
Qed.

Lemma magree_store_left:
  forall m1 m2 P chunk b ofs v1 m1',
  magree m1 m2 P ->
  Mem.store chunk m1 b ofs v1 = Some m1' ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> ~(P b i)) ->
  magree m1' m2 P.
Proof.
  intros. eapply magree_storebytes_left; eauto.
  eapply Mem.store_storebytes; eauto.
  intros. rewrite encode_val_length in H2.
  rewrite <- size_chunk_conv in H2. apply H1; auto.
Qed.

Lemma magree_free:
  forall m1 m2 (P Q: locset) b lo hi m1',
  magree m1 m2 P ->
  Mem.free m1 b lo hi = Some m1' ->
  (forall b' i, Q b' i ->
                b' <> b \/ ~(lo <= i < hi) ->
                P b' i) ->
  exists m2', Mem.free m2 b lo hi = Some m2' /\ magree m1' m2' Q.
Proof.
  intros.
  destruct (Mem.range_perm_free m2 b lo hi) as [m2' FREE].
  red; intros. eapply ma_perm; eauto. eapply Mem.free_range_perm; eauto.
  exists m2'; split; auto.
  constructor; intros.
- (* permissions *)
  assert (Mem.perm m2 b0 ofs k p). { eapply ma_perm; eauto. eapply Mem.perm_free_3; eauto. }
  exploit Mem.perm_free_inv; eauto. intros [[A B] | A]; auto.
  subst b0. eelim Mem.perm_free_2. eexact H0. eauto. eauto.
- (* inverse permissions *)
  exploit ma_perm_inv; eauto using Mem.perm_free_3. intros [A|A].
  eapply Mem.perm_free_inv in A; eauto. destruct A as [[A B] | A]; auto.
  subst b0; right; eapply Mem.perm_free_2; eauto.
  right; intuition eauto using Mem.perm_free_3.
- (* contents *)
  rewrite (Mem.free_result _ _ _ _ _ H0).
  rewrite (Mem.free_result _ _ _ _ _ FREE).
  simpl. eapply ma_memval; eauto. eapply Mem.perm_free_3; eauto.
  apply H1; auto. destruct (eq_block b0 b); auto.
  subst b0. right. red; intros. eelim Mem.perm_free_2. eexact H0. eauto. eauto.
- (* nextblock *)
  rewrite (Mem.free_result _ _ _ _ _ H0).
  rewrite (Mem.free_result _ _ _ _ _ FREE).
  simpl. eapply ma_nextblock; eauto.
Qed.

Lemma magree_valid_access:
  forall m1 m2 (P: locset) chunk b ofs p,
  magree m1 m2 P ->
  Mem.valid_access m1 chunk b ofs p ->
  Mem.valid_access m2 chunk b ofs p.
Proof.
  intros. destruct H0; split; auto.
  red; intros. eapply ma_perm; eauto.
Qed.

(** * Properties of the need environment *)

Lemma add_need_all_eagree:
  forall e e' r ne,
  eagree e e' (add_need_all r ne) -> eagree e e' ne.
Proof.
  intros; red; intros. generalize (H r0). unfold add_need_all.
  rewrite NE.gsspec. destruct (peq r0 r); auto with na.
Qed.

Lemma add_need_all_lessdef:
  forall e e' r ne,
  eagree e e' (add_need_all r ne) -> Val.lessdef e#r e'#r.
Proof.
  intros. generalize (H r); unfold add_need_all.
  rewrite NE.gsspec, peq_true. auto with na.
Qed.

Lemma add_need_eagree:
  forall e e' r nv ne,
  eagree e e' (add_need r nv ne) -> eagree e e' ne.
Proof.
  intros; red; intros. generalize (H r0); unfold add_need.
  rewrite NE.gsspec. destruct (peq r0 r); auto.
  subst r0. intros. eapply nge_agree; eauto. apply nge_lub_r.
Qed.

Lemma add_need_vagree:
  forall e e' r nv ne,
  eagree e e' (add_need r nv ne) -> vagree e#r e'#r nv.
Proof.
  intros. generalize (H r); unfold add_need.
  rewrite NE.gsspec, peq_true. intros. eapply nge_agree; eauto. apply nge_lub_l.
Qed.

Lemma add_needs_all_eagree:
  forall rl e e' ne,
  eagree e e' (add_needs_all rl ne) -> eagree e e' ne.
Proof.
  induction rl; simpl; intros.
  auto.
  apply IHrl. eapply add_need_all_eagree; eauto.
Qed.

Lemma add_needs_all_lessdef:
  forall rl e e' ne,
  eagree e e' (add_needs_all rl ne) -> Val.lessdef_list e##rl e'##rl.
Proof.
  induction rl; simpl; intros.
  constructor.
  constructor. eapply add_need_all_lessdef; eauto.
  eapply IHrl. eapply add_need_all_eagree; eauto.
Qed.

Lemma add_needs_eagree:
  forall rl nvl e e' ne,
  eagree e e' (add_needs rl nvl ne) -> eagree e e' ne.
Proof.
  induction rl; simpl; intros.
  auto.
  destruct nvl. apply add_needs_all_eagree with (a :: rl); auto.
  eapply IHrl. eapply add_need_eagree; eauto.
Qed.

Lemma add_needs_vagree:
  forall rl nvl e e' ne,
  eagree e e' (add_needs rl nvl ne) -> vagree_list e##rl e'##rl nvl.
Proof.
  induction rl; simpl; intros.
  constructor.
  destruct nvl.
  apply vagree_lessdef_list. eapply add_needs_all_lessdef with (rl := a :: rl); eauto.
  constructor. eapply add_need_vagree; eauto.
  eapply IHrl. eapply add_need_eagree; eauto.
Qed.

Lemma add_ros_need_eagree:
  forall e e' ros ne, eagree e e' (add_ros_need_all ros ne) -> eagree e e' ne.
Proof.
  intros. destruct ros; simpl in *. eapply add_need_all_eagree; eauto. auto.
Qed.

Global Hint Resolve add_need_all_eagree add_need_all_lessdef
             add_need_eagree add_need_vagree
             add_needs_all_eagree add_needs_all_lessdef
             add_needs_eagree add_needs_vagree
             add_ros_need_eagree: na.

Lemma eagree_init_regs:
  forall rl vl1 vl2 ne,
  Val.lessdef_list vl1 vl2 ->
  eagree (init_regs vl1 rl) (init_regs vl2 rl) ne.
Proof.
  induction rl; intros until ne; intros LD; simpl.
- red; auto with na.
- inv LD.
  + red; auto with na.
  + apply eagree_update; auto with na.
Qed.

(** * Basic properties of the translation *)

Section PRESERVATION.

Variable prog: program.
Variable tprog: RTL_Incomplete.program.

(* To make math_prog antitone *)
Hypothesis COMPLETE_TPROG : is_complete tprog.
Hypothesis TRANSF: match_prog_aux transf_function prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_match TRANSF).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_match TRANSF).

Lemma functions_translated:
  forall (v: val) (f: RTL.fundef),
  Genv.find_funct ge v = Some f ->
  exists cu tf,
  Genv.find_funct tge v = Some tf /\ transf_fundef (romem_for cu) f = OK tf /\ linkorder cu prog.
Proof (Genv.find_funct_match TRANSF).

Lemma function_ptr_translated:
  forall (b: block) (f: RTL.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists cu tf,
  Genv.find_funct_ptr tge b = Some tf /\ transf_fundef (romem_for cu) f = OK tf /\ linkorder cu prog.
Proof (Genv.find_funct_ptr_match TRANSF).

Lemma sig_function_translated:
  forall rm f tf,
  AST.transf_partial_fundef (transf_function rm) f = OK tf ->
  RTL_Incomplete.funsig tf = funsig f.
Proof.
  intros; destruct f; monadInv H.
  unfold transf_function in EQ.
  destruct (analyze (ValueAnalysis.analyze rm f) f); inv EQ; auto.
  auto.
Qed.

Lemma stacksize_translated:
  forall rm f tf,
  transf_function rm f = OK tf -> tf.(fn_stacksize) = f.(fn_stacksize).
Proof.
  unfold transf_function; intros. destruct (analyze (ValueAnalysis.analyze rm f) f); inv H; auto.
Qed.

Definition vanalyze (cu: program) (f: function) :=
  ValueAnalysis.analyze (romem_for cu) f.

Lemma transf_function_at:
  forall cu f tf an pc instr,
  transf_function (romem_for cu) f = OK tf ->
  analyze (vanalyze cu f) f = Some an ->
  f.(fn_code)!pc = Some instr ->
  tf.(fn_code)!pc = Some(transf_instr (vanalyze cu f) an pc instr).
Proof.
  intros. unfold transf_function in H. unfold vanalyze in H0. rewrite H0 in H. inv H; simpl.
  rewrite PTree.gmap. rewrite H1; auto.
Qed.

Lemma is_dead_sound_1:
  forall nv, is_dead nv = true -> nv = Nothing.
Proof.
  destruct nv; simpl; congruence.
Qed.

Lemma is_dead_sound_2:
  forall nv, is_dead nv = false -> nv <> Nothing.
Proof.
  intros; red; intros. subst nv; discriminate.
Qed.

Hint Resolve is_dead_sound_1 is_dead_sound_2: na.

Lemma is_int_zero_sound:
  forall nv, is_int_zero nv = true -> nv = I Int.zero.
Proof.
  unfold is_int_zero; destruct nv; try discriminate.
  predSpec Int.eq Int.eq_spec m Int.zero; congruence.
Qed.

Lemma find_function_translated:
  forall ros rs fd trs ne,
  find_function ge ros rs = Some fd ->
  eagree rs trs (add_ros_need_all ros ne) ->
  exists cu tfd,
     RTL_Incomplete.find_function tge ros trs = Some tfd
  /\ AST.transf_partial_fundef (transf_function (romem_for cu)) fd = OK tfd
  /\ linkorder cu prog.
Proof.
  intros. destruct ros as [r|id]; simpl in *.
- assert (LD: Val.lessdef rs#r trs#r) by eauto with na. inv LD.
  apply functions_translated; auto.
  rewrite <- H2 in H; discriminate.
- rewrite symbols_preserved. destruct (Genv.find_symbol ge id); try discriminate.
  apply function_ptr_translated; auto.
Qed.

(** * Semantic invariant *)




Inductive gen_match_stackframes {B} (R : res (@function_ B) -> res (@function_ B) -> Prop) (transf_f : romem -> function -> res (@function_ B)): stackframe -> stackframe -> Prop :=
  | gen_match_stackframes_intro:
      forall res f sp pc e tf te cu an
        (LINK: linkorder cu prog)
        (FUN: R (transf_f (romem_for cu) f) (OK tf))
        (ANL: analyze (vanalyze cu f) f = Some an)
        (RES: forall v tv,
              Val.lessdef v tv ->
              eagree (e#res <- v) (te#res<- tv)
                     (fst (transfer f (vanalyze cu f) pc an!!pc))),
      gen_match_stackframes R transf_f (Stackframe res f (Vptr sp Ptrofs.zero) pc e)
                        (Stackframe res tf (Vptr sp Ptrofs.zero) pc te).

Definition match_stackframes {B} := @gen_match_stackframes B eq.



#[local, refine] 
Instance monoMatchStackframes S1 S2 : IncRef (fun transf_f => match_stackframes transf_f S1 S2) :=
{ 
  ir_mono := fun tf => gen_match_stackframes (fun x y => y ⊑ x) tf S1 S2 ;
  ir_anti := fun tf => gen_match_stackframes (fun tf1 tf2 => is_complete tf1 /\ tf1 = tf2) tf S1 S2;
}.
Proof.
  - intros tf tf' Hprec MS; inv MS; econstructor; eauto.
    eapply is_transitive; eauto.
    apply Hprec; eauto. 
  - intros tf tf' Hprec MS; inv MS; econstructor; eauto. 
    destruct FUN. 
    unfold_refinement in Hprec.
    specialize (Hprec (romem_for cu) f). eapply is_complete_minimal in Hprec; eauto.
    rewrite Hprec. split; eauto.

  - intros tf MS. inv MS; econstructor; eauto. rewrite <- FUN. reflexivity.
    
  - intros tf MS; inv MS; econstructor; eauto. destruct FUN as [_ <-]. reflexivity.

  - intros tf ? MS; inv MS; econstructor; eauto. symmetry.
    apply is_complete_minimal; eauto. apply H; eauto.
      
  - intros tf HC MS; inv MS; econstructor; eauto; split.
    * apply HC; eauto.
    * rewrite FUN; reflexivity.
Defined.

Inductive gen_match_states  
  (R : res RTL_Incomplete.function -> res RTL_Incomplete.function -> Prop) 
  (transf_f : romem -> function -> res RTL_Incomplete.function) :
    state -> RTL_Incomplete.state -> Prop := 

| gen_match_regular_states:
forall s f sp pc e m ts tf te tm cu an
  (STACKS: list_forall2 (gen_match_stackframes R transf_f) s ts)
  (LINK: linkorder cu prog)
  (FUN: R (transf_f (romem_for cu) f) (OK tf))
  (ANL: analyze (vanalyze cu f) f = Some an)
  (ENV: eagree e te (fst (transfer f (vanalyze cu f) pc an!!pc)))
  (MEM: magree m tm (nlive ge sp (snd (transfer f (vanalyze cu f) pc an!!pc)))),
  gen_match_states R transf_f (State s f (Vptr sp Ptrofs.zero) pc e m) (State ts tf (Vptr sp Ptrofs.zero) pc te tm)
  
| gen_match_call_states:
  forall s f args m ts tf targs tm cu
    (STACKS: list_forall2 (gen_match_stackframes R transf_f) s ts)
    (LINK: linkorder cu prog)
    (FUN: transf_fundef (romem_for cu) f = OK tf)
    (ARGS: Val.lessdef_list args targs)
    (MEM: Mem.extends m tm),
  gen_match_states R transf_f (Callstate s f args m)
               (Callstate ts tf targs tm)

| gen_match_return_states:
  forall s v m ts tv tm
    (STACKS: list_forall2 (gen_match_stackframes R transf_f) s ts)
    (RES: Val.lessdef v tv)
    (MEM: Mem.extends m tm),
  gen_match_states R transf_f (Returnstate s v m)
               (Returnstate ts tv tm).

Definition match_states := gen_match_states eq.



Lemma list_forall2_impl : forall {A B} {P Q : A -> B -> Prop} {l1 l2},
  (forall x y, P x y -> Q x y) ->
  list_forall2 P l1 l2 -> list_forall2 Q l1 l2.
Proof.
  intros ? ? ? ? l1; induction l1; intros [] HPQ HP; try inv HP; econstructor; eauto.
Qed.

Lemma list_forall2_antitone : forall {A B} {P Q : A -> B -> Prop} {l1 l2},
  (forall x y, P x y -> Q x y) ->
  list_forall2 P l1 l2 -> list_forall2 Q l1 l2.
Proof.
  intros ? ? ? ? l1; induction l1; intros [] HPQ HP; try inv HP; econstructor; eauto.
(* Qed. *)
Abort.

Lemma gen_match_stackframes_ref:
  forall {tf tf' S1 S2}, tf ⊑ tf' -> gen_match_stackframes (fun x y => y ⊑ x) tf S1 S2 -> gen_match_stackframes (fun x y => y ⊑ x) tf' S1 S2.
Proof.
  intros. inv H0. econstructor; eauto. eapply is_transitive; eauto. apply H; eauto.
Qed.

Lemma gen_match_stackframes_ref_eq:
  forall {tf S1 S2}, is_complete tf -> gen_match_stackframes (fun x y => y ⊑ x) tf S1 S2 -> gen_match_stackframes eq tf S1 S2.
Proof.
  intros ? ? ? HC H; inv H; econstructor; eauto.
  symmetry; apply is_complete_minimal; eauto.
  apply HC; eauto. 
Qed.

Lemma gen_match_stackframes_complete_eq_eq:
  forall {tf S1 S2}, gen_match_stackframes (fun x y => is_complete x /\ x = y) tf S1 S2 -> gen_match_stackframes eq tf S1 S2.
Proof.
  intros ? ? ? H; inv H; econstructor; eauto; destruct FUN; eauto.
Qed.

Lemma gen_match_stackframes_eq_ref :
  forall {tf S1 S2}, gen_match_stackframes eq tf S1 S2 -> gen_match_stackframes (fun x y => y ⊑ x) tf S1 S2.
Proof.
  intros ? ? ? H; inv H; econstructor; eauto.
  rewrite <- FUN. reflexivity.
Qed.
    
Lemma gen_match_stackframes_eq_complete_eq:
  forall {tf S1 S2}, is_complete tf -> gen_match_stackframes eq tf S1 S2 -> gen_match_stackframes (fun x y => is_complete x /\ x = y) tf S1 S2.
Proof.
  intros ? ? ? HC H; inv H; econstructor; eauto; split; eauto.
  apply HC; eauto. 
Qed.

Lemma gen_match_stackframes_monotone_complete :
  forall {tf tf' S1 S2}, tf ⊑ tf' -> gen_match_stackframes (fun x y => is_complete x /\ x = y) tf' S1 S2 -> gen_match_stackframes (fun x y => is_complete x /\ x = y) tf S1 S2.
Proof.
  intros. inv H0. econstructor; eauto. destruct_ctx.
  unfold_refinement in H.
  specialize (H (romem_for cu) f). 
  eapply is_complete_minimal in H; eauto. rewrite H; eauto.
Qed.

Lemma gen_match_stackframes_complete_monotone :
  forall {tf S1 S2}, gen_match_stackframes (fun x y => is_complete x /\ x = y) tf S1 S2 -> gen_match_stackframes (fun x y => y ⊑ x) tf S1 S2.
Proof.
  intros.  inv H. econstructor; eauto. destruct_ctx.
  rewrite <- FUN1. reflexivity.
Qed.

#[local, refine] 
Instance IncRefMatchStates S1 S2 : IncRef (fun transf_f => match_states transf_f S1 S2) :=
{ 
  ir_mono := fun tf => gen_match_states (fun x y => y ⊑ x) tf S1 S2 ;
  ir_anti := fun tf => gen_match_states (fun tf1 tf2 => is_complete tf1 /\ tf1 = tf2) tf S1 S2;
}.
Proof.
  - intros tf tf' Hprec MS; inv MS; econstructor; eauto. 
    * unshelve eapply (list_forall2_impl _ STACKS). intros ? ? Hgms. unshelve eapply (gen_match_stackframes_ref _ Hgms). eauto.
    * eapply is_transitive; eauto; apply Hprec.
    * unshelve eapply (list_forall2_impl _ STACKS). intros ? ? Hgms; unshelve eapply (gen_match_stackframes_ref _ Hgms); eauto.
    * unshelve eapply (list_forall2_impl _ STACKS). intros ? ? Hgms; unshelve eapply (gen_match_stackframes_ref _ Hgms); eauto.

  - intros tf tf' Hprec MS; inv MS; econstructor; eauto.
    * unshelve eapply (list_forall2_impl _ STACKS). intros ? ? Hgms; unshelve eapply (gen_match_stackframes_monotone_complete _ Hgms); eauto.
    * unfold_refinement in Hprec. destruct_ctx.
      specialize (Hprec (romem_for cu) f).
      eapply is_complete_minimal in Hprec; eauto. rewrite Hprec; eauto.
    * unshelve eapply (list_forall2_impl _ STACKS). intros ? ? Hgms; unshelve eapply (gen_match_stackframes_monotone_complete _ Hgms); eauto.
    * unshelve eapply (list_forall2_impl _ STACKS). intros ? ? Hgms; unshelve eapply (gen_match_stackframes_monotone_complete _ Hgms); eauto.

  - intros tf MS; inv MS; econstructor; eauto.
    * unshelve eapply (list_forall2_impl _ STACKS). intros ? ? Hgms.
      apply (gen_match_stackframes_eq_ref Hgms); eauto.
    * rewrite FUN. reflexivity.
    * unshelve eapply (list_forall2_impl _ STACKS). intros ? ? Hgms.
      apply (gen_match_stackframes_eq_ref Hgms); eauto.
      * unshelve eapply (list_forall2_impl _ STACKS). intros ? ? Hgms.
      apply (gen_match_stackframes_eq_ref Hgms); eauto.
    
  - intros tf MS; inv MS; econstructor; eauto.
    * unshelve eapply (list_forall2_impl _ STACKS). intros ? ? Hgms.
      eapply (gen_match_stackframes_complete_eq_eq Hgms); eauto.
    * destruct FUN; eauto.
    * unshelve eapply (list_forall2_impl _ STACKS). intros ? ? Hgms.
      eapply (gen_match_stackframes_complete_eq_eq Hgms); eauto.
    * unshelve eapply (list_forall2_impl _ STACKS). intros ? ? Hgms.
      eapply (gen_match_stackframes_complete_eq_eq Hgms); eauto.

   - intros tf ? MS; inv MS; econstructor; eauto.
    * unshelve eapply (list_forall2_impl _ STACKS). intros ? ? Hgms; unshelve eapply (gen_match_stackframes_ref_eq _ Hgms); eauto.
    * symmetry; apply is_complete_minimal; eauto; apply H; eauto.
    * unshelve eapply (list_forall2_impl _ STACKS). intros ? ? Hgms; unshelve eapply (gen_match_stackframes_ref_eq _ Hgms); eauto.
    * unshelve eapply (list_forall2_impl _ STACKS). intros ? ? Hgms; unshelve eapply (gen_match_stackframes_ref_eq _ Hgms); eauto.

  - intros tf HC MS; inv MS; econstructor; eauto.
    * unshelve eapply (list_forall2_impl _ STACKS). intros ? ? Hgms; unshelve eapply (gen_match_stackframes_eq_complete_eq _ Hgms); eauto.
    * split; eauto. apply HC; eauto. 
    * unshelve eapply (list_forall2_impl _ STACKS). intros ? ? Hgms; unshelve eapply (gen_match_stackframes_eq_complete_eq _ Hgms); eauto.
    * unshelve eapply (list_forall2_impl _ STACKS). intros ? ? Hgms; unshelve eapply (gen_match_stackframes_eq_complete_eq _ Hgms); eauto.
Defined.      

Lemma analyze_successors:
  forall cu f an pc instr pc',
  analyze (vanalyze cu f) f = Some an ->
  f.(fn_code)!pc = Some instr ->
  In pc' (successors_instr instr) ->
  NA.ge an!!pc (transfer f (vanalyze cu f) pc' an!!pc').
Proof.
  intros. eapply DS.fixpoint_solution; eauto.
  intros. unfold transfer; rewrite H2. destruct a. apply DS.L.eq_refl.
Qed.


Definition match_succ_states_stm (transf_f : romem -> function -> res RTL_Incomplete.function) :=
  forall s f sp pc e m ts tf te tm an pc' cu instr ne nm
    (LINK: linkorder cu prog)
    (STACKS: list_forall2 (match_stackframes transf_f) s ts)
    (FUN: transf_f (romem_for cu) f = OK tf)
    (ANL: analyze (vanalyze cu f) f = Some an)
    (INSTR: f.(fn_code)!pc = Some instr)
    (SUCC: In pc' (successors_instr instr))
    (ANPC: an!!pc = (ne, nm))
    (ENV: eagree e te ne)
    (MEM: magree m tm (nlive ge sp nm)),
  match_states  transf_f (State s f (Vptr sp Ptrofs.zero) pc' e m)
               (State ts tf (Vptr sp Ptrofs.zero) pc' te tm).



Instance : IncRef match_succ_states_stm.
Proof.
  unfold match_succ_states_stm.
  repeat (unshelve eapply IncRefForall; intros).
  unshelve eapply IncRefArrow.
  unshelve eapply IncRefArrow.
  unshelve eapply IncRefEqL.
  - unfold_complete. intros ? Hc. apply Hc; eauto.
  - unfold is_monotone; intros ? ? Hprec; apply Hprec.
Defined.

Lemma match_succ_states : ir_mono match_succ_states_stm transf_function.
Proof.
  simpl.
  intros s f sp pc e m ts tf te tm an pc' cu instr ne nm LINK STACKS FUN ANL INSTR SUCC ANPC ENV MEM.
   (* START NEW *) 
  destruct FUN.
  (* END NEW *)
  exploit analyze_successors; eauto. rewrite ANPC; simpl; intros [A B].
   (* rewrite ANPC; simpl. intros [A B]. *)
  econstructor; eauto.
  (* START NEW : Changes from original proof *)
  - eapply list_forall2_impl; [|eauto]. intros; eapply gen_match_stackframes_complete_monotone; eauto.
  - rewrite <- H0. reflexivity.
  (* END NEW *)
  - eapply eagree_ge; eauto.
  - eapply magree_monotone; eauto.
Qed.

(* FROM HERE : They remain  the same *)
(** Builtin arguments and results *)

Lemma eagree_set_res:
  forall e1 e2 v1 v2 res ne,
  Val.lessdef v1 v2 ->
  eagree e1 e2 (kill_builtin_res res ne) ->
  eagree (regmap_setres res v1 e1) (regmap_setres res v2 e2) ne.
Proof.
  intros. destruct res; simpl in *; auto.
  apply eagree_update; eauto. apply vagree_lessdef; auto.
Qed.

Lemma transfer_builtin_arg_sound:
  forall bc e e' sp m m' a v,
  eval_builtin_arg ge (fun r => e#r) (Vptr sp Ptrofs.zero) m a v ->
  forall nv ne1 nm1 ne2 nm2,
  transfer_builtin_arg nv (ne1, nm1) a = (ne2, nm2) ->
  eagree e e' ne2 ->
  magree m m' (nlive ge sp nm2) ->
  genv_match bc ge ->
  bc sp = BCstack ->
  exists v',
     eval_builtin_arg ge (fun r => e'#r) (Vptr sp Ptrofs.zero) m' a  v'
  /\ vagree v v' nv
  /\ eagree e e' ne1
  /\ magree m m' (nlive ge sp nm1).
Proof.
  induction 1; simpl; intros until nm2; intros TR EA MA GM SPM; inv TR.
- exists e'#x; intuition auto. constructor. eauto 2 with na. eauto 2 with na.
- exists (Vint n); intuition auto. constructor. apply vagree_same.
- exists (Vlong n); intuition auto. constructor. apply vagree_same.
- exists (Vfloat n); intuition auto. constructor. apply vagree_same.
- exists (Vsingle n); intuition auto. constructor. apply vagree_same.
- simpl in H. exploit magree_load; eauto.
  intros. eapply nlive_add; eauto with va. rewrite Ptrofs.add_zero_l in H0; auto.
  intros (v' & A & B).
  exists v'; intuition auto. constructor; auto. apply vagree_lessdef; auto.
  eapply magree_monotone; eauto. intros; eapply incl_nmem_add; eauto.
- exists (Vptr sp (Ptrofs.add Ptrofs.zero ofs)); intuition auto with na. constructor.
- unfold Senv.symbol_address in H; simpl in H.
  destruct (Genv.find_symbol ge id) as [b|] eqn:FS; simpl in H; try discriminate.
  exploit magree_load; eauto.
  intros. eapply nlive_add; eauto. constructor. apply GM; auto.
  intros (v' & A & B).
  exists v'; intuition auto.
  constructor. simpl. unfold Senv.symbol_address; simpl; rewrite FS; auto.
  apply vagree_lessdef; auto.
  eapply magree_monotone; eauto. intros; eapply incl_nmem_add; eauto.
- exists (Senv.symbol_address ge id ofs); intuition auto with na. constructor.
- destruct (transfer_builtin_arg All (ne1, nm1) hi) as [ne' nm'] eqn:TR.
  exploit IHeval_builtin_arg2; eauto. intros (vlo' & A & B & C & D).
  exploit IHeval_builtin_arg1; eauto. intros (vhi' & P & Q & R & S).
  exists (Val.longofwords vhi' vlo'); intuition auto.
  constructor; auto.
  apply vagree_lessdef.
  apply Val.longofwords_lessdef; apply lessdef_vagree; auto.
- destruct (transfer_builtin_arg All (ne1, nm1) a1) as [ne' nm'] eqn:TR.
  exploit IHeval_builtin_arg2; eauto. intros (v2' & A & B & C & D).
  exploit IHeval_builtin_arg1; eauto. intros (v1' & P & Q & R & S).
  econstructor; intuition auto.
  econstructor; eauto.
  destruct Archi.ptr64; auto using Val.add_lessdef, Val.addl_lessdef, vagree_lessdef, lessdef_vagree.
Qed.

Lemma transfer_builtin_args_sound:
  forall e sp m e' m' bc al vl,
  eval_builtin_args ge (fun r => e#r) (Vptr sp Ptrofs.zero) m al vl ->
  forall ne1 nm1 ne2 nm2,
  transfer_builtin_args (ne1, nm1) al = (ne2, nm2) ->
  eagree e e' ne2 ->
  magree m m' (nlive ge sp nm2) ->
  genv_match bc ge ->
  bc sp = BCstack ->
  exists vl',
     eval_builtin_args ge (fun r => e'#r) (Vptr sp Ptrofs.zero) m' al vl'
  /\ Val.lessdef_list vl vl'
  /\ eagree e e' ne1
  /\ magree m m' (nlive ge sp nm1).
Proof.
Local Opaque transfer_builtin_arg.
  induction 1; simpl; intros.
- inv H. exists (@nil val); intuition auto. constructor.
- destruct (transfer_builtin_arg All (ne1, nm1) a1) as [ne' nm'] eqn:TR.
  exploit IHlist_forall2; eauto. intros (vs' & A1 & B1 & C1 & D1).
  exploit transfer_builtin_arg_sound; eauto. intros (v1' & A2 & B2 & C2 & D2).
  exists (v1' :: vs'); intuition auto. constructor; auto.
Qed.

Lemma can_eval_builtin_arg:
  forall sp e m e' m' P,
  magree m m' P ->
  forall a v,
  eval_builtin_arg ge (fun r => e#r) (Vptr sp Ptrofs.zero) m a v ->
  exists v', eval_builtin_arg tge (fun r => e'#r) (Vptr sp Ptrofs.zero) m' a v'.
Proof.
  intros until P; intros MA.
  assert (LD: forall chunk addr v,
              Mem.loadv chunk m addr = Some v ->
              exists v', Mem.loadv chunk m' addr = Some v').
  {
    intros. destruct addr; simpl in H; try discriminate.
    eapply Mem.valid_access_load. eapply magree_valid_access; eauto.
    eapply Mem.load_valid_access; eauto. }
  induction 1; try (econstructor; now constructor).
- exploit LD; eauto. intros (v' & A). exists v'; constructor; auto.
- exploit LD; eauto. intros (v' & A). exists v'; constructor.
  unfold Senv.symbol_address, Senv.find_symbol. rewrite symbols_preserved. assumption.
- destruct IHeval_builtin_arg1 as (v1' & A1).
  destruct IHeval_builtin_arg2 as (v2' & A2).
  exists (Val.longofwords v1' v2'); constructor; auto.
- destruct IHeval_builtin_arg1 as (v1' & A1).
  destruct IHeval_builtin_arg2 as (v2' & A2).
  econstructor; econstructor; eauto.
Qed.

Lemma can_eval_builtin_args:
  forall sp e m e' m' P,
  magree m m' P ->
  forall al vl,
  eval_builtin_args ge (fun r => e#r) (Vptr sp Ptrofs.zero) m al vl ->
  exists vl', eval_builtin_args tge (fun r => e'#r) (Vptr sp Ptrofs.zero) m' al vl'.
Proof.
  induction 2.
- exists (@nil val); constructor.
- exploit can_eval_builtin_arg; eauto. intros (v' & A).
  destruct IHlist_forall2 as (vl' & B).
  exists (v' :: vl'); constructor; eauto.
Qed.

(** Properties of volatile memory accesses *)

Lemma transf_volatile_store:
  forall v1 v2 v1' v2' m tm chunk sp nm t v m',
  volatile_store_sem chunk ge (v1::v2::nil) m t v m' ->
  Val.lessdef v1 v1' ->
  vagree v2 v2' (store_argument chunk) ->
  magree m tm (nlive ge sp nm) ->
  v = Vundef /\
  exists tm', volatile_store_sem chunk ge (v1'::v2'::nil) tm t Vundef tm'
           /\ magree m' tm' (nlive ge sp nm).
Proof.
  intros. inv H. split; auto.
  inv H0. inv H9.
- (* volatile *)
  exists tm; split; auto. econstructor. econstructor; eauto.
  eapply eventval_match_lessdef; eauto. apply store_argument_load_result; auto.
- (* not volatile *)
  exploit magree_store_parallel. eauto. eauto. eauto.
  instantiate (1 := nlive ge sp nm). auto.
  intros (tm' & P & Q).
  exists tm'; split. econstructor. econstructor; eauto. auto.
Qed.

Lemma eagree_set_undef:
  forall e1 e2 ne r, eagree e1 e2 ne -> eagree (e1#r <- Vundef) e2 ne.
Proof.
  intros; red; intros. rewrite PMap.gsspec. destruct (peq r0 r); auto with na.
Qed.
(* UNTIL HERE : They remain the same *)


Definition step_simulation_pred (transf_f : romem -> function -> res RTL_Incomplete.function) :=
  forall S1 t S2, step ge S1 t S2 ->
  forall S1', match_states transf_f S1 S1' -> sound_state prog S1 ->
  exists S2', RTL_Incomplete.step tge S1' t S2' /\ match_states transf_f S2 S2'.

Lemma inc_step_simulation : ir_mono step_simulation_pred transf_function.
Proof. 
  simpl.
Ltac TransfInstr :=
  match goal with
  | [INSTR: (fn_code _)!_ = Some _,
     FUN: transf_function _ _ = OK _,
     ANL: analyze _ _ = Some _ |- _ ] =>
       generalize (transf_function_at _ _ _ _ _ _ FUN ANL INSTR);
       let TI := fresh "TI" in
       intro TI; unfold transf_instr in TI
  end.

Ltac UseTransfer :=
  match goal with
  | [INSTR: (fn_code _)!?pc = Some _,
     ANL: analyze _ _ = Some ?an |- _ ] =>
       destruct (an!!pc) as [ne nm] eqn:ANPC;
       unfold transfer in *;
       rewrite INSTR in *;
       simpl in *
  end.

  induction 1; intros S1' MS SS; inv MS; simpl.

  - (* nop *)  
  (* NEW *) destruct FUN as [? FUN].
  TransfInstr; UseTransfer.
  econstructor; split.
  eapply RTL_Incomplete.exec_Inop; eauto.
  eapply match_succ_states; eauto; simpl; auto.
  
  - (* op *) 
    destruct FUN as [? FUN].
    TransfInstr.
    rewrite FUN in H1.
    clear -TI H1.
    unfold_complete in H1. unfold_complete in H1. destruct_ctx.
    unfold_complete in H3. specialize (H3 pc). unfold_complete in H3.
    destruct ((fn_code tf) ! pc); try discriminate.
    inversion TI; subst. inversion H3.
    
  (* Proof of complete code for this branch *)
  (* UseTransfer.
  destruct (is_dead (nreg ne res)) eqn:DEAD;
  [idtac|destruct (is_int_zero (nreg ne res)) eqn:INTZERO;
  [idtac|destruct (operation_is_redundant op (nreg ne res)) eqn:REDUNDANT]].
+ (* dead instruction, turned into a nop *)
  econstructor; split. 
  eapply exec_Inop; eauto.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update_dead; auto with na.
+ (* instruction with needs = [I Int.zero], turned into a load immediate of zero. *)
  econstructor; split.
  eapply RTL_Incomplete.exec_Iop with (v := Vint Int.zero); eauto.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update; auto.
  rewrite is_int_zero_sound by auto.
  destruct v; simpl; auto. apply iagree_zero.
+ (* redundant operation *)
  destruct args.
  * (* kept as is because no arguments -- should never happen *)
  simpl in *.
  exploit needs_of_operation_sound. eapply ma_perm; eauto.
  eauto. instantiate (1 := nreg ne res). eauto with na. eauto with na. intros [tv [A B]].
  econstructor; split.
  eapply RTL_Incomplete.exec_Iop with (v := tv); eauto.
  rewrite <- A. apply eval_operation_preserved. exact symbols_preserved.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update; auto.
  * (* turned into a move *)
  unfold fst in ENV. unfold snd in MEM. simpl in H0.
  assert (VA: vagree v te#r (nreg ne res)).
  { eapply operation_is_redundant_sound with (arg1' := te#r) (args' := te##args).
    eauto. eauto. exploit add_needs_vagree; eauto. }
  econstructor; split.
  eapply RTL_Incomplete.exec_Iop; eauto. simpl; reflexivity.
  eapply match_succ_states; eauto. simpl; auto.
  eapply eagree_update; eauto 2 with na.
+ (* preserved operation *)
  simpl in *.
  exploit needs_of_operation_sound. eapply ma_perm; eauto. eauto. eauto 2 with na. eauto with na.
  intros [tv [A B]].
  econstructor; split.
  eapply RTL_Incomplete.exec_Iop with (v := tv); eauto.
  rewrite <- A. apply eval_operation_preserved. exact symbols_preserved.
  eapply match_succ_states; eauto. simpl; auto.
  apply eagree_update; eauto 2 with na. *)

- (* load *)
    destruct FUN as [? FUN].
    TransfInstr; UseTransfer.
    destruct (is_dead (nreg ne dst)) eqn:DEAD;
    [idtac|destruct (is_int_zero (nreg ne dst)) eqn:INTZERO];
    simpl in *.
+ (* dead instruction, turned into a nop *)
  econstructor; split.
  eapply RTL_Incomplete.exec_Inop; eauto.
  eapply match_succ_states; eauto; simpl; auto. 
  apply eagree_update_dead; auto with na.
  Unshelve. all: eauto.
+ (* instruction with needs = [I Int.zero], turned into a load immediate of zero. *)
  econstructor; split.
  eapply RTL_Incomplete.exec_Iop with (v := Vint Int.zero); eauto.
  eapply match_succ_states; eauto; simpl; auto.
  apply eagree_update; auto.
  rewrite is_int_zero_sound by auto.
  destruct v; simpl; auto. apply iagree_zero.

+ (* preserved *)
  exploit eval_addressing_lessdef. eapply add_needs_all_lessdef; eauto. eauto.
  intros (ta & U & V). inv V; try discriminate.
  destruct ta; simpl in H1; try discriminate.
  exploit magree_load; eauto.
  exploit aaddressing_sound; eauto. intros (bc & A & B & C).
  intros. apply nlive_add with bc i; assumption.
  intros (tv & P & Q).
  econstructor; split.
  eapply RTL_Incomplete.exec_Iload with (a := Vptr b i). eauto.
  rewrite <- U. apply eval_addressing_preserved. exact symbols_preserved.
  eauto.
  eapply match_succ_states; eauto; simpl; auto.
  apply eagree_update; eauto 2 with na.
  eapply magree_monotone; eauto. intros. apply incl_nmem_add; auto.

- (* store *)
  destruct FUN as [? FUN]. 
  TransfInstr; UseTransfer.
  destruct (nmem_contains nm (aaddressing (vanalyze cu f) # pc addr args)
             (size_chunk chunk)) eqn:CONTAINS.
+ (* preserved *)
  simpl in *.
  exploit eval_addressing_lessdef. eapply add_needs_all_lessdef; eauto. eauto.
  intros (ta & U & V). inv V; try discriminate.
  destruct ta; simpl in H1; try discriminate.
  exploit magree_store_parallel. eauto. eauto. instantiate (1 := te#src). eauto with na.
  instantiate (1 := nlive ge sp0 nm).
  exploit aaddressing_sound; eauto. intros (bc & A & B & C).
  intros. apply nlive_remove with bc b i; assumption.
  intros (tm' & P & Q).
  econstructor; split.
  eapply RTL_Incomplete.exec_Istore with (a := Vptr b i). eauto.
  rewrite <- U. apply eval_addressing_preserved. exact symbols_preserved.
  eauto.
  eapply match_succ_states; eauto; simpl; auto.
  eauto 3 with na.

+ (* dead instruction, turned into a nop *)
  destruct a; simpl in H1; try discriminate.
  econstructor; split.
  eapply RTL_Incomplete.exec_Inop; eauto.
  eapply match_succ_states; eauto; simpl; auto.
  eapply magree_store_left; eauto.
  exploit aaddressing_sound; eauto. intros (bc & A & B & C).
  intros. eapply nlive_contains; eauto.

- (* call *)
  destruct FUN as [? FUN].
  TransfInstr; UseTransfer.
  exploit find_function_translated; eauto 2 with na. intros (cu' & tfd & A & B & C).
  econstructor; split.
  eapply RTL_Incomplete.exec_Icall; eauto. eapply sig_function_translated; eauto.
  eapply gen_match_call_states with (cu := cu'); eauto.
  (* new case *)
  unfold_complete in COMPLETE_TPROG. destruct COMPLETE_TPROG as [COMPLETE_TPROG' _]. specialize (COMPLETE_TPROG' ros te). unfold tge in A. erewrite A in COMPLETE_TPROG'. eauto.
  
  constructor; auto. eapply gen_match_stackframes_intro with (cu := cu); eauto.
  (* new case *) 
  rewrite <- FUN. reflexivity.
  intros.
  edestruct analyze_successors; eauto. simpl; eauto.
  eapply eagree_ge; eauto. rewrite ANPC. simpl.
  apply eagree_update; eauto with na.
  (* new case *) 
  eapply list_forall2_impl; [| eauto]. intros; eapply gen_match_stackframes_complete_monotone; eauto.
  eauto 2 with na.
  eapply magree_extends; eauto. apply nlive_all.

- (* tailcall *)
  destruct FUN as [? FUN]. 
  TransfInstr; UseTransfer.
  exploit find_function_translated; eauto 2 with na. intros (cu' & tfd & A & B & L).
  exploit magree_free. eauto. eauto. instantiate (1 := nlive ge stk nmem_all).
  intros; eapply nlive_dead_stack; eauto.
  intros (tm' & C & D).
  econstructor; split.
  eapply RTL_Incomplete.exec_Itailcall; eauto. eapply sig_function_translated; eauto.
  erewrite stacksize_translated by eauto. eexact C.
  eapply gen_match_call_states with (cu := cu'); eauto 2 with na.
  (* new case *)
  unfold_complete in COMPLETE_TPROG. destruct COMPLETE_TPROG as [COMPLETE_TPROG' _]. specialize (COMPLETE_TPROG' ros te). unfold tge in A. erewrite A in COMPLETE_TPROG'. eauto.
  eapply list_forall2_impl; [| eauto]. intros; eapply gen_match_stackframes_complete_monotone; eauto.
  eapply magree_extends; eauto. apply nlive_all.

- (* builtin *)
  destruct FUN as [HC FUN].
  TransfInstr; UseTransfer. revert ENV MEM TI.
  functional induction (transfer_builtin (vanalyze cu f)#pc ef args res ne nm);
  simpl in *; intros.
+ (* volatile load *)
  inv H0. inv H6. rename b1 into v1.
  destruct (transfer_builtin_arg All
              (kill_builtin_res res ne,
              nmem_add nm (aaddr_arg (vanalyze cu f) # pc a1)
                (size_chunk chunk)) a1) as (ne1, nm1) eqn: TR.
  InvSoundState. exploit transfer_builtin_arg_sound; eauto.
  intros (tv1 & A & B & C & D).
  inv H1. simpl in B. inv B.
  assert (X: exists tvres, volatile_load ge chunk tm b ofs t tvres /\ Val.lessdef vres tvres).
  {
    inv H2.
  * exists (Val.load_result chunk v); split; auto. constructor; auto.
  * exploit magree_load; eauto.
    exploit aaddr_arg_sound_1; eauto. rewrite <- AN. intros.
    intros. eapply nlive_add; eassumption.
    intros (tv & P & Q).
    exists tv; split; auto. constructor; auto.
  }
  destruct X as (tvres & P & Q).
  econstructor; split.
  eapply RTL_Incomplete.exec_Ibuiltin; eauto.
  apply eval_builtin_args_preserved with (ge1 := ge). exact symbols_preserved.
  constructor. eauto. constructor.
  eapply external_call_symbols_preserved. apply senv_preserved.
  constructor. simpl. eauto.
  eapply match_succ_states; eauto; simpl; auto.
  apply eagree_set_res; auto.
  eapply magree_monotone; eauto. intros. apply incl_nmem_add; auto.
  

+ (* volatile store *)
  inv H0. inv H6. inv H7. rename b1 into v1. rename b0 into v2.
  destruct (transfer_builtin_arg (store_argument chunk)
              (kill_builtin_res res ne, nm) a2) as (ne2, nm2) eqn: TR2.
  destruct (transfer_builtin_arg All (ne2, nm2) a1) as (ne1, nm1) eqn: TR1.
  InvSoundState.
  exploit transfer_builtin_arg_sound. eexact H4. eauto. eauto. eauto. eauto. eauto.
  intros (tv1 & A1 & B1 & C1 & D1).
  exploit transfer_builtin_arg_sound. eexact H3. eauto. eauto. eauto. eauto. eauto.
  intros (tv2 & A2 & B2 & C2 & D2).
  exploit transf_volatile_store; eauto.
  intros (EQ & tm' & P & Q). subst vres.
  econstructor; split.
  eapply RTL_Incomplete.exec_Ibuiltin; eauto.
  apply eval_builtin_args_preserved with (ge1 := ge). exact symbols_preserved.
  constructor. eauto. constructor. eauto. constructor.
  eapply external_call_symbols_preserved. apply senv_preserved.
  simpl; eauto.
  eapply match_succ_states; eauto; simpl; auto.
  apply eagree_set_res; auto.
  

+ (* memcpy *)
  rewrite e1 in TI.
  inv H0. inv H6. inv H7. rename b1 into v1. rename b0 into v2.
  set (adst := aaddr_arg (vanalyze cu f) # pc dst) in *.
  set (asrc := aaddr_arg (vanalyze cu f) # pc src) in *.
  destruct (transfer_builtin_arg All
              (kill_builtin_res res ne,
               nmem_add (nmem_remove nm adst sz) asrc sz) dst)
           as (ne2, nm2) eqn: TR2.
  destruct (transfer_builtin_arg All (ne2, nm2) src) as (ne1, nm1) eqn: TR1.
  InvSoundState.
  exploit transfer_builtin_arg_sound. eexact H3. eauto. eauto. eauto. eauto. eauto.
  intros (tv1 & A1 & B1 & C1 & D1).
  exploit transfer_builtin_arg_sound. eexact H4. eauto. eauto. eauto. eauto. eauto.
  intros (tv2 & A2 & B2 & C2 & D2).
  inv H1.
  exploit magree_loadbytes. eauto. eauto.
  intros. eapply nlive_add; eauto.
  unfold asrc, vanalyze. rewrite AN; eapply aaddr_arg_sound_1; eauto.
  intros (tbytes & P & Q).
  exploit magree_storebytes_parallel.
  eapply magree_monotone. eexact D2.
  instantiate (1 := nlive ge sp0 (nmem_remove nm adst sz)).
  intros. apply incl_nmem_add; auto.
  eauto.
  instantiate (1 := nlive ge sp0 nm).
  intros. eapply nlive_remove; eauto.
  unfold adst, vanalyze; rewrite AN; eapply aaddr_arg_sound_1; eauto.
  erewrite Mem.loadbytes_length in H1 by eauto.
  rewrite Z2Nat.id in H1 by lia. auto.
  eauto.
  intros (tm' & A & B).
  econstructor; split.
  eapply RTL_Incomplete.exec_Ibuiltin; eauto.
  apply eval_builtin_args_preserved with (ge1 := ge). exact symbols_preserved.
  constructor. eauto. constructor. eauto. constructor.
  eapply external_call_symbols_preserved. apply senv_preserved.
  simpl in B1; inv B1. simpl in B2; inv B2. econstructor; eauto.
  eapply match_succ_states; eauto; simpl; auto.
  apply eagree_set_res; auto.
  

+ (* memcpy eliminated *)
  rewrite e1 in TI.
  inv H0. inv H6. inv H7. rename b1 into v1. rename b0 into v2.
  set (adst := aaddr_arg (vanalyze cu f) # pc dst) in *.
  set (asrc := aaddr_arg (vanalyze cu f) # pc src) in *.
  inv H1.
  econstructor; split.
  eapply RTL_Incomplete.exec_Inop; eauto.
  eapply match_succ_states; eauto; simpl; auto.
  destruct res; auto. apply eagree_set_undef; auto.
  eapply magree_storebytes_left; eauto.
  clear H3.
  exploit aaddr_arg_sound; eauto.
  intros (bc & A & B & C).
  intros. eapply nlive_contains; eauto.
  erewrite Mem.loadbytes_length in H0 by eauto.
  rewrite Z2Nat.id in H0 by lia. auto.
  

+ (* annot *)
  destruct (transfer_builtin_args (kill_builtin_res res ne, nm) _x2) as (ne1, nm1) eqn:TR.
  InvSoundState.
  exploit transfer_builtin_args_sound; eauto. intros (tvl & A & B & C & D).
  inv H1.
  econstructor; split.
  eapply RTL_Incomplete.exec_Ibuiltin; eauto.
  apply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
  eapply external_call_symbols_preserved. apply senv_preserved.
  constructor. eapply eventval_list_match_lessdef; eauto 2 with na.
  eapply match_succ_states; eauto; simpl; auto.
  apply eagree_set_res; auto.
  

+ (* annot val *)
  destruct (transfer_builtin_args (kill_builtin_res res ne, nm) _x2) as (ne1, nm1) eqn:TR.
  InvSoundState.
  exploit transfer_builtin_args_sound; eauto. intros (tvl & A & B & C & D).
  inv H1. inv B. inv H6.
  econstructor; split.
  eapply RTL_Incomplete.exec_Ibuiltin; eauto.
  apply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
  eapply external_call_symbols_preserved. apply senv_preserved.
  constructor.
  eapply eventval_match_lessdef; eauto 2 with na.
  eapply match_succ_states; eauto; simpl; auto.
  apply eagree_set_res; auto.
  

+ (* debug *)
  inv H1.
  exploit can_eval_builtin_args; eauto. intros (vargs' & A).
  econstructor; split.
  eapply RTL_Incomplete.exec_Ibuiltin; eauto. constructor.
  eapply match_succ_states; eauto; simpl; auto.
  apply eagree_set_res; auto.
  

+ (* all other builtins *)
  assert ((fn_code tf)!pc = Some(RTL_Incomplete.Ibuiltin _x _x0 res pc')).
  {
    destruct _x; auto. destruct _x0; auto. destruct _x0; auto. destruct _x0; auto. contradiction.
  }
  clear y TI.
  destruct (transfer_builtin_args (kill_builtin_res res ne, nmem_all) _x0) as (ne1, nm1) eqn:TR.
  InvSoundState.
  exploit transfer_builtin_args_sound; eauto. intros (tvl & A & B & C & D).
  exploit external_call_mem_extends; eauto 2 with na.
  eapply magree_extends; eauto. intros. apply nlive_all.
  intros (v' & tm' & P & Q & R & S).
  econstructor; split.
  eapply RTL_Incomplete.exec_Ibuiltin; eauto.
  apply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
  eapply external_call_symbols_preserved. apply senv_preserved. eauto.
  eapply match_succ_states; eauto; simpl; auto.
  apply eagree_set_res; auto.
  eapply mextends_agree; eauto.
  

- (* conditional *)
  destruct FUN as [? FUN].
  TransfInstr; UseTransfer. destruct (peq ifso ifnot).
+ replace (if b then ifso else ifnot) with ifso by (destruct b; congruence).
  econstructor; split.
  eapply RTL_Incomplete.exec_Inop; eauto.
  eapply match_succ_states; eauto; simpl; auto.
+ econstructor; split.
  eapply RTL_Incomplete.exec_Icond; eauto.
  eapply needs_of_condition_sound. eapply ma_perm; eauto. eauto. eauto with na.
  eapply match_succ_states; eauto 2 with na. (* new *) simpl; eauto.
  simpl; destruct b; auto.

- (* jumptable *)
  destruct FUN as [? FUN].
  TransfInstr; UseTransfer.
  assert (LD: Val.lessdef rs#arg te#arg) by eauto 2 with na.
  rewrite H0 in LD. inv LD.
  econstructor; split.
  eapply RTL_Incomplete.exec_Ijumptable; eauto.
  eapply match_succ_states; eauto 2 with na. (* new *) simpl; eauto.
  simpl. eapply list_nth_z_in; eauto.
  Unshelve. all: eauto.

- (* return *)
  destruct FUN as [? FUN].
  TransfInstr; UseTransfer.
  exploit magree_free. eauto. eauto. instantiate (1 := nlive ge stk nmem_all).
  intros; eapply nlive_dead_stack; eauto.
  intros (tm' & A & B).
  econstructor; split.
  eapply RTL_Incomplete.exec_Ireturn; eauto.
  erewrite stacksize_translated by eauto. eexact A.
  constructor; auto.
  (* forall2 *)
  eapply list_forall2_impl; [| eauto]. intros; eapply gen_match_stackframes_complete_monotone; eauto.
  destruct or; simpl; eauto 2 with na.
  eapply magree_extends; eauto. apply nlive_all.

- (* internal function *)
  monadInv FUN. generalize EQ. unfold transf_function. fold (vanalyze cu f). intros EQ'.
  destruct (analyze (vanalyze cu f) f) as [an|] eqn:AN; inv EQ'.
  exploit Mem.alloc_extends; eauto. apply Z.le_refl. apply Z.le_refl.
  intros (tm' & A & B).
  econstructor; split.
  econstructor; simpl; eauto.
  simpl. econstructor; eauto. 
  (* new case *)
  eapply list_forall2_impl; [| eauto]. intros; eapply gen_match_stackframes_complete_monotone; eauto.
  fold (transf_function (romem_for cu) f).
  rewrite EQ. reflexivity.
  apply eagree_init_regs; auto.
  apply mextends_agree; auto.

- (* external function *)
  
  exploit external_call_mem_extends; eauto.
  intros (res' & tm' & A & B & C & D).
  simpl in FUN. inv FUN.
  econstructor; split.
  econstructor; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  econstructor; eauto. 
  eapply list_forall2_impl; [| eauto]. intros; eapply gen_match_stackframes_complete_monotone; eauto.

- (* return *)
  inv STACKS. inv H1.
  destruct FUN as [? FUN].
  econstructor; split.
  constructor.
  econstructor; eauto.
  (* forall2 *)
  eapply list_forall2_impl; [| eauto]. intros; eapply gen_match_stackframes_complete_monotone; eauto.

  rewrite <- FUN. reflexivity.
  apply mextends_agree; auto.
Qed.

(** * The simulation diagram *)

Theorem step_simulation:
  is_complete transf_function -> 
  forall S1 t S2, step ge S1 t S2 ->
  forall S1', match_states transf_function S1 S1' -> sound_state prog S1 ->
  exists S2', RTL_Incomplete.step tge S1' t S2' /\ match_states transf_function S2 S2'.
Proof.
  intros COMPLETE.
  change (step_simulation_pred transf_function).
  rewrite <- complete_monotone_is_equivalent; eauto.
  apply inc_step_simulation.
Qed.

Lemma transf_initial_states:
  forall st1, initial_state prog st1 ->
  exists st2, initial_state tprog st2 /\ match_states transf_function st1 st2.
Proof.
  intros. inversion H.
  exploit function_ptr_translated; eauto. intros (cu & tf & A & B & C).
  exists (Callstate nil tf nil m0); split.
  econstructor; eauto.
  eapply (Genv.init_mem_match TRANSF); eauto.
  replace (prog_main tprog) with (prog_main prog).
  rewrite symbols_preserved. eauto.
  symmetry; eapply match_program_main; eauto.
  rewrite <- H3. eapply sig_function_translated; eauto.
  econstructor; eauto. constructor. apply Mem.extends_refl.
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states transf_function st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H. inv STACKS. inv RES. constructor.
Qed.

(** * Semantic preservation *)
(* Cannot yet be defined because it expects complete RTL programs.
    i.e. tprog : RTL.program, not tprog : RTL_Incomplete.program 
    
    This theorem is of particular interest for the final compiler correctness
    proof. During the incremental process, and while this optimization is not finished, 
    the final compiler stack of passes should simply not include unfinished passes.
    *)

(* Theorem transf_program_correct:
  forward_simulation (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  intros.
  apply forward_simulation_step with
     (match_states := fun s1 s2 => sound_state prog s1 /\ match_states s1 s2).
- apply senv_preserved.
- simpl; intros. exploit transf_initial_states; eauto. intros [st2 [A B]].
  exists st2; intuition. eapply sound_initial; eauto.
- simpl; intros. destruct H. eapply transf_final_states; eauto.
- simpl; intros. destruct H0.
  assert (sound_state prog s1') by (eapply sound_step; eauto).
  fold ge; fold tge. exploit step_simulation; eauto. intros [st2' [A B]].
  exists st2'; auto.
Qed. *)

End PRESERVATION.

(* The following is additional code related to an approach to opting-out from RTL_Incomplete into RTL. 
We assume that the function is complete and we try to obtain the transf_program_correct proof. 
The opting-out process, without deleting and replacing the code, requires transforming from 
RTL_Incomplete to RTL, preserving several properties.


One thing that it requires in particular, is the addition of an `is_complete` premise in the 
`gen_match_call_states` constructor of `gen_match_states` (currently commented out).
This needs to be propagated to related definitions, such as `gen_match_succ_states`.
In total, one needs to add the following parameter to `gen_match_states` and arg to the constructor:
`{Complete (@fundef_ B)}
is_complete tf 

Adding this premise still preserves the previous `step_simulation` proof without any changes, 
however we leave it out because it is not truly necessary for the incremental process we want 
to illustrate.

Note that the opting-out is quite convoluted and requires a lot of manual work,
which amounts to ~550 LOC (maybe someone more familiar with CompCert could do it in a simpler way)
*)

(** * BEGINNING OPTING-OUT *)
(*
Axiom (is_complete_transf_function : is_complete transf_function).

Hint Resolve is_complete_transf_function : core.

Lemma is_complete_to_RTL_Incomplete_fundef f : is_complete (to_RTL_Incomplete_fundef f).
Proof.
  destruct f; red; cbn.
  - unfold_complete. repeat split.
    +  induction (fn_params f); unfold_complete; eauto. split; eauto.
    unfold_complete; eauto.
    + unfold_complete. intro. rewrite PTree.gmap. unfold option_map.
    destruct (_ ! _); unfold_complete; eauto. destruct i; econstructor; eauto; try now (unfold_complete; eauto).
    all: try induction l; unfold_complete; eauto; try split; unfold_complete; eauto.
    1-2: destruct s0; eauto.
    destruct o; eauto.   
  - unfold_complete; eauto.
Qed. 

Lemma Tree_map_node (A B : Type) (f : A -> B) (l r : PTree.tree A) o : 
  PTree.map (fun _ => f) (PTree.Node l o r) = PTree.Node (PTree.map (fun _ => f) l) (option_map f o) (PTree.map (fun _ => f) r).
Proof.
  eapply PTree.extensionality; intro p.
  rewrite PTree.gmap; repeat rewrite PTree.gNode. destruct p; repeat rewrite PTree.gmap; unfold option_map; try destruct (_ ! _); eauto.
Qed. 

Definition to_RTL_code (f : RTL_Incomplete.code) (Hfcomplete : is_complete f): 
  { ff : RTL.code | PTree.map (fun _ => to_RTL_Incomplete_instruction) ff = f}.
Proof.
  unfold_complete in Hfcomplete. revert Hfcomplete. 
  induction f using PTree.tree_ind.
  - exists PTree.Empty; eauto.  
  - intro Hfcomplete. unshelve eexists (PTree.Node _ _ _). 
    * apply IHf. intros. specialize (Hfcomplete (xO pc)).
      rewrite PTree.gNode in Hfcomplete. eauto.
    * destruct o; [| exact None].
      refine (Some _).
      eapply (to_RTL_instruction i). 
      unfold_complete in Hfcomplete. specialize (Hfcomplete xH).
      rewrite PTree.gNode in Hfcomplete. unfold_complete in Hfcomplete.
      inversion Hfcomplete; intro; try discriminate.      
    * apply IHf0. intros. specialize (Hfcomplete (xI pc)).
      rewrite PTree.gNode in Hfcomplete. eauto.
    * rewrite Tree_map_node. cbn. f_equal.
      + destruct IHf; eauto.   
      + destruct o; cbn; eauto. f_equal. cbn in H. eapply to_RTL_Incomplete_instruction_retract.
      + destruct IHf0; eauto.   
Qed.

Program Definition to_RTL_function (f : RTL_Incomplete.function) (Hfcomplete : is_complete f): 
  { ff : RTL.function | to_RTL_Incomplete_function ff = f} :=  
  exist _ (mkfunction (fn_sig f) (fn_params f) (fn_stacksize f) _ (fn_entrypoint f)) _.
Next Obligation.
  unfold_complete in Hfcomplete. destruct_ctx. 
  eapply to_RTL_code; eauto. 
Defined. 
Next Obligation.  
  destruct f; cbn. unfold to_RTL_Incomplete_function, map_function_; cbn. f_equal.
  unfold_complete in Hfcomplete. destruct_ctx.
  unfold to_RTL_function_obligation_1. cbn.  
  destruct to_RTL_code;  eauto.
Qed. 

Program Definition transf_function_complete (r : romem) (f : function) : res function :=
  match transf_function r f as tf return is_complete tf -> res function with
  | OK tf => fun H => OK (to_RTL_function tf H)
  | Error msg => fun _ => Error msg
  end _.
Next Obligation.
  pose proof (H := is_complete_transf_function). apply H; eauto.
Defined.

Definition  bind_pure {A B} (f : A -> B) (a:res A) :=
  bind a (fun a => OK (f a)).

Lemma transf_function_complete_spec r f : 
  bind_pure to_RTL_Incomplete_function (transf_function_complete r f) = 
  transf_function r f.
Proof.
  unfold bind_pure, bind, transf_function_complete, transf_function_complete_obligation_1.
  set is_complete_transf_function.
  set (i _ _ _ _). clearbody i0. 
  set (transf_function r f) in *. destruct r0; eauto.
  f_equal. destruct f0. destruct to_RTL_function; eauto.
Qed. 

Definition transf_stack_complete r s := map_state (transf_function_complete r) s.

Lemma transf_stack_complete_spec r s : 
  map_state (bind_pure to_RTL_Incomplete_function) (transf_stack_complete r s) = 
  map_state (transf_function r) s.
Proof.
  unfold transf_stack_complete. rewrite map_state_compose.
  eapply map_state_ext, transf_function_complete_spec.
Qed. 


Lemma transf_function_complete_to_RTL r f tf : 
  transf_function_complete r f = OK tf -> 
  transf_function r f = OK (to_RTL_Incomplete_function tf).
Proof. 
  intros EQ. unfold transf_function_complete, transf_function_complete_obligation_1 in *.  
  set is_complete_transf_function in EQ.
  set (i _ _ _ _) in *. clearbody i0. destruct transf_function; inversion EQ; cbn.  repeat f_equal.
  destruct f0; unfold to_RTL_Incomplete_function, map_function_; f_equal; cbn in *.
  eapply PTree.extensionality; intro p. rewrite PTree.gmap. unfold option_map.
  unfold to_RTL_function_obligation_1. destruct i0, a, a, a. cbn.  destruct to_RTL_code; cbn.
  rewrite <- e. now erewrite PTree.gmap.
Qed. 

Lemma transf_function_complete_to_RTL_error r f e : 
  transf_function_complete r f = Error e -> 
  transf_function r f = Error e.
Proof. 
  intros EQ. unfold transf_function_complete, transf_function_complete_obligation_1 in *.  
  set is_complete_transf_function in EQ. 
  set (i _ _ _ _) in *. clearbody i0. destruct transf_function; inversion EQ; cbn.  repeat f_equal.
Qed. 

Lemma transf_fundef_complete_to_RTL r f tf : 
  transf_partial_fundef (transf_function_complete r) f = OK tf -> 
  transf_partial_fundef (transf_function r) f = OK (AST.transf_fundef to_RTL_Incomplete_function tf).
Proof. 
  destruct f; intro H; cbn in *. 
  - monadInv H. eapply transf_function_complete_to_RTL in EQ. now rewrite EQ.
  - destruct tf; inversion H; subst; eauto.
Qed.  

Lemma transf_function_complete_to_RTL_inv r f tf : 
  transf_function r f = OK tf ->
  exists tf', tf = to_RTL_Incomplete_function tf' /\ transf_function_complete r f = OK tf'.
Proof. 
  intro H. 
  pose (tf' := transf_function_complete r f).
  case_eq tf'; intros ? Htf'. 
  - pose proof (H' := Htf'). eapply transf_function_complete_to_RTL in Htf'. exists f0. 
    split; eauto. destruct transf_function; inversion H; inversion Htf'; now subst.
  - eapply transf_function_complete_to_RTL_error in Htf'. rewrite H in Htf'; inversion Htf'.
Qed.

Lemma transf_fundef_complete_to_RTL_inv r f tf : 
  transf_partial_fundef (transf_function r) f = OK tf ->
  exists tf', tf = to_RTL_Incomplete_fundef tf' /\ transf_partial_fundef (transf_function_complete r) f = OK tf'.
Proof. 
  intro H. destruct f; cbn in *. 
  - case_eq (transf_function r f); intros ? Hf; rewrite Hf in H; inversion H; subst. 
    eapply transf_function_complete_to_RTL_inv in Hf as [tf' [? ? ]].
    exists (Internal tf'). subst. now rewrite H1.
  - inversion H; subst. exists (External e); split; eauto.
Qed. 

(* Defined so Compiler.v works, fixing the transf_f function to the concrete one  *)
Definition match_prog (prog : program) (tprog: program) :=
  match_prog_aux transf_function_complete prog tprog.

Section TRANSF_PROGRAM_CORRECT.
  Variable prog: program.
  Variable tprog: program.
  Hypothesis TRANSF: match_prog prog tprog.
  Let ge := Genv.globalenv prog.
  Let tge := Genv.globalenv tprog.
    
  Definition tprog' := transform_program to_RTL_Incomplete_fundef tprog.

  Lemma match_tprog' : match_program (fun _ f tf => tf = to_RTL_Incomplete_fundef f) eq tprog tprog'.
  Proof. 
    eapply match_transform_program.
  Qed.  

  Lemma find_funct_ptr_tprog' b : match Genv.find_funct_ptr (Genv.globalenv tprog') b with
  | Some x => is_complete x
  | None => True
  end.
  Proof. 
  set (Genv.find_funct_ptr _ b). case_eq o; eauto. intro f.
  unfold o. eapply Genv.find_funct_ptr_prop.
  unfold tprog'. destruct tprog; cbn. clear. intros.
  eapply list_in_map_inv in H as [[] [? _]]. cbn in *.
  destruct g; inversion H; subst. eapply is_complete_to_RTL_Incomplete_fundef.
  Qed. 

  Lemma iscomplete_tprog' : is_complete tprog'.
  Proof.
    split; intros; red; cbn -[Genv.globalenv].
    - destruct ros;  cbn -[Genv.globalenv].
      + destruct (rs#r); cbn -[Genv.globalenv]; eauto. destruct (Ptrofs.eq_dec); eauto.
        eapply find_funct_ptr_tprog'.
      + destruct Genv.find_symbol; eauto.
         eapply find_funct_ptr_tprog'.
    - eapply find_funct_ptr_tprog'.
  Qed.

  Lemma match_prog_tprog' : match_prog_aux transf_function prog tprog'.
  Proof.
    destruct TRANSF as [? [? ?]].
    repeat split.
    2-3: unfold tprog'; destruct tprog; eauto.
    unfold tprog'. destruct tprog; cbn in *. clear H0 H1. clear TRANSF. 
    induction H; cbn; econstructor; eauto.
    clear - H. unfold match_ident_globdef in *. destruct H.
    split.
    - destruct b1, g; cbn; eauto.
    - destruct a1, b1; cbn in *. inversion H0; subst; econstructor; eauto.
      destruct f1; cbn in *.
      2: { inversion H2. f_equal. }
      case_eq (transf_function_complete (romem_for ctx') f); intros; rewrite H in H2; inversion H2.
      eapply transf_function_complete_to_RTL in H. now rewrite H.
  Qed. 

  Lemma senv_preserved': Senv.equiv ge tge.
  Proof (Genv.senv_match TRANSF).

  Lemma state_to_RTL_Incomplete : forall s1 s2,
    match_states prog transf_function_complete transf_function_complete s1 s2 ->
    match_states prog transf_function transf_function s1 (map_state to_RTL_Incomplete_instruction s2).
  Proof.
    intros s1 s2; inversion 1; subst; cbn.  
    - econstructor 1; eauto. 
      + eapply list_forall2_map. eapply list_forall2_impl; [|eauto].
        intros. inversion H0; subst; econstructor; eauto.
        eapply transf_function_complete_to_RTL; eauto.
      + eapply transf_function_complete_to_RTL; eauto.
    - econstructor 2; eauto.
      + eapply is_complete_to_RTL_Incomplete_fundef.
      + eapply list_forall2_map. eapply list_forall2_impl; [|eauto].
        intros. inversion H0; subst; econstructor; eauto.
        eapply transf_function_complete_to_RTL; eauto.
      + eapply transf_fundef_complete_to_RTL; eauto.
    - econstructor 3; eauto. 
      eapply list_forall2_map. eapply list_forall2_impl; [|eauto].
      intros. inversion H0; subst; econstructor; eauto.
      eapply transf_function_complete_to_RTL; eauto.
  Qed.

  Lemma stakeframe_inversion s ts :
    gen_match_stackframes prog eq transf_function s ts ->
    exists ts', 
    gen_match_stackframes prog eq transf_function_complete s ts' /\
    ts = map_stackframe to_RTL_Incomplete_function ts'.
    Proof.
      inversion 1; subst; eauto. pose proof (FUN' := FUN).
      eapply transf_function_complete_to_RTL_inv in FUN as [tf' [? ?]].
      exists (Stackframe res tf' (Vptr sp Ptrofs.zero) pc te).
      split; cbn; try econstructor; eauto. now f_equal.
    Qed. 

  Lemma stakeframes_inversion s ts :
    list_forall2 (gen_match_stackframes prog eq transf_function) s ts ->
    exists ts', 
    list_forall2 (gen_match_stackframes prog eq transf_function_complete) s ts' /\
    ts = map (map_stackframe to_RTL_Incomplete_function) ts'.
  Proof.
    induction 1.
    - exists nil. repeat econstructor.
    - eapply stakeframe_inversion in H as [b' [? ?]].
      destruct IHlist_forall2 as [bs [? ?]].
      exists (b' :: bs). split; cbn; try econstructor; try f_equal; eauto.
  Qed.  

  Lemma state_inversion : forall s1 s2,
    match_states prog transf_function transf_function s1 s2 ->
    exists s2', match_states prog transf_function_complete transf_function_complete s1 s2' /\
                s2 = map_state to_RTL_Incomplete_instruction s2'.
  Proof.
    intros s1 s2; inversion 1; subst; cbn. 
    - eapply stakeframes_inversion in STACKS as [s' [? ?]].
      eapply transf_function_complete_to_RTL_inv in FUN as [f' [? ? ]].
      exists (State s' f' (Vptr sp Ptrofs.zero) pc te tm). cbn; split; try econstructor; try f_equal; eauto.
    - eapply stakeframes_inversion in STACKS as [s' [? ?]].
      eapply transf_fundef_complete_to_RTL_inv in FUN as [f' [? ? ]].
      exists (Callstate s' f' targs tm). cbn; split; try econstructor; try f_equal; eauto.
      destruct f'; repeat unfold_complete; eauto.
    - eapply stakeframes_inversion in STACKS as [s' [? ?]].
      exists (Returnstate s' tv tm). cbn; split; try econstructor; try f_equal; eauto.
  Qed. 

  Lemma find_symbol_tprog' id 
    (Linker := Linker_prog (AST.fundef (@function_ instruction)) unit): 
    Genv.find_symbol (Genv.globalenv tprog') id = 
    Genv.find_symbol (Genv.globalenv tprog) id.
  Proof.
    pose proof match_tprog'; pose proof match_prog_tprog'.
    unfold match_prog, match_prog_aux, match_program in *. 
    etransitivity.
    - eapply Genv.find_symbol_match; eauto.
    - symmetry. eapply Genv.find_symbol_match; eauto.
  Qed.    

  Lemma eval_operation_tprog' sp op rs args m: 
    eval_operation (Genv.globalenv tprog') sp op rs ## args m = eval_operation (Genv.globalenv tprog) sp op rs ## args m.
  Proof.
    eapply eval_operation_preserved. apply find_symbol_tprog'.
  Qed.

  Lemma eval_addressing_tprog' sp addr rs args: 
    eval_addressing (Genv.globalenv tprog') sp addr rs ## args = eval_addressing (Genv.globalenv tprog) sp addr rs ## args.
  Proof.
    eapply eval_addressing_preserved. apply find_symbol_tprog'.
  Qed.
  
  Lemma find_function_tprog' ros rs f
    (Linker := Linker_prog (AST.fundef (@function_ instruction)) unit) :  
    RTL_Incomplete.find_function (Genv.globalenv tprog') ros rs = Some (to_RTL_Incomplete_fundef f) ->
    find_function (Genv.globalenv tprog) ros rs = Some f.
  Proof.
    pose proof (Hprog := match_tprog').
    destruct ros; intro H; cbn -[tprog'] in *.
    - unfold Genv.find_funct in *.
      destruct (_ # _); inversion H. clear H1. destruct (Ptrofs.eq_dec _ _); inversion H. clear H1; subst.  
      unfold Genv.find_funct_ptr in *. 
      pose proof (Genv.find_def_match_2 Hprog b).
      unfold fundef_ in *. 
      set (Genv.find_def (Genv.globalenv tprog') b) in *.
      destruct o; [|inversion H]. inversion H0; subst. 
      inversion H3; subst; f_equal. inversion H. now eapply to_RTL_Incomplete_fundef_injective.
      inversion H.
    - erewrite <- find_symbol_tprog'. destruct (Genv.find_symbol _ _); inversion H.
    unfold Genv.find_funct_ptr in *. 
    pose proof (Genv.find_def_match_2 Hprog b).
    unfold fundef_ in *. 
    set (Genv.find_def (Genv.globalenv tprog') b) in *. clear H1. 
    destruct o; [|inversion H]. inversion H0; subst. 
    inversion H3; subst; f_equal. inversion H. now eapply to_RTL_Incomplete_fundef_injective.
    inversion H.
  Qed. 

  Lemma symbol_address_tprog' id ofs : 
    Senv.symbol_address (Genv.globalenv tprog') id ofs = Senv.symbol_address (Genv.globalenv tprog) id ofs.
  Proof.
    unfold Senv.symbol_address. unfold Senv.find_symbol. cbn - [tprog']. 
    rewrite find_symbol_tprog'; eauto.
  Qed.   

  Lemma eval_builtin_args_tprog' rs sp m args vargs : 
    eval_builtin_args (Genv.globalenv tprog') (fun r : positive => rs # r) sp m args vargs ->
    eval_builtin_args (Genv.globalenv tprog) (fun r : positive => rs # r) sp m args vargs.
  Proof.
    unfold eval_builtin_args. eapply list_forall2_impl; intros.
    induction H; subst; try econstructor; eauto.
    - now rewrite <- symbol_address_tprog'.
    - rewrite symbol_address_tprog'. econstructor.
  Qed. 

  Lemma find_var_info_tprog' b : 
    Genv.find_var_info (Genv.globalenv tprog') b = Genv.find_var_info (Genv.globalenv tprog) b.
  Proof.
    unfold Genv.find_var_info.  pose proof (Hprog := match_tprog').
    pose proof (Genv.find_def_match_2 Hprog b).
    set (Genv.find_def (Genv.globalenv tprog') b) in *.
    case_eq (Genv.find_def (Genv.globalenv tprog) b). 
    - intros ? He. cbn in *. unfold fundef_ in He. rewrite He in H.
      inversion H. subst. inversion H2. subst; eauto. inversion H0; subst; eauto.         
    - intros He. unfold fundef_ in He. rewrite He in H.
      inversion H; eauto.
  Qed.

  Lemma external_call_tprog' ef vargs m t vres m' : 
    external_call ef (Genv.globalenv tprog') vargs m t vres m' ->
    external_call ef (Genv.globalenv tprog) vargs m t vres m'.
  Proof.
    eapply external_call_symbols_preserved.
    unfold Senv.equiv. repeat split; intros; eauto.
    - unfold Senv.find_symbol. cbn - [tprog']. now rewrite find_symbol_tprog'.
    - unfold Senv.public_symbol. cbn - [tprog']. unfold Genv.public_symbol. rewrite find_symbol_tprog'. 
      destruct (Genv.find_symbol _ _); eauto. now repeat rewrite Genv.globalenv_public.
    - unfold Senv.block_is_volatile. cbn. unfold Genv.block_is_volatile.
      now rewrite find_var_info_tprog'.
  Qed. 

  Lemma step_simul s s' t : RTL_Incomplete.step (Genv.globalenv (transform_program to_RTL_Incomplete_fundef tprog))
        (map_state to_RTL_Incomplete_instruction s) t
        (map_state to_RTL_Incomplete_instruction s') -> step (Genv.globalenv tprog) s t s'.
  Proof.
  inversion 1; clear H.  
  + destruct s, s'; cbn in *; inversion H0; inversion H1; subst; clear H0 H1.
    apply to_RTL_Incomplete_function_injective in H11. 
    apply stack_to_RTL_Incomplete_function_injective in H10; subst. 
    econstructor 1. cbn in H3. rewrite PTree.gmap in H3. unfold option_map in H3. destruct (_ ! _) ; inversion H3; f_equal; eauto. 
    destruct i; inversion H0; eauto.  
  + destruct s, s'; cbn in *; inversion H0; inversion H1; subst; clear H0 H1.
    apply to_RTL_Incomplete_function_injective in H12. 
    apply stack_to_RTL_Incomplete_function_injective in H11; subst. 
    econstructor 2. cbn in H2. rewrite PTree.gmap in H2. unfold option_map in H2. destruct (_ ! _) ; inversion H2; f_equal; eauto. 
    destruct i; inversion H0; eauto.
    now rewrite <- eval_operation_tprog'. 
  + destruct s, s'; cbn in *; inversion H0; inversion H1; subst; clear H0 H1.
    apply to_RTL_Incomplete_function_injective in H13. 
    apply stack_to_RTL_Incomplete_function_injective in H12; subst. 
    econstructor 3; eauto. cbn in H2. rewrite PTree.gmap in H2. unfold option_map in H2. destruct (_ ! _) ; inversion H2; f_equal; eauto. 
    destruct i; inversion H0; eauto.
    now rewrite <- eval_addressing_tprog'. 
  + destruct s, s'; cbn in *; inversion H0; inversion H1; subst; clear H0 H1.
    apply to_RTL_Incomplete_function_injective in H13. 
    apply stack_to_RTL_Incomplete_function_injective in H12; subst. 
    econstructor 4; eauto. cbn in H2. rewrite PTree.gmap in H2. unfold option_map in H2. destruct (_ ! _) ; inversion H2; f_equal; eauto. 
    destruct i; inversion H0; eauto.
    now rewrite <- eval_addressing_tprog'. 
  + destruct s, s'; cbn in *; inversion H0; inversion H1; subst; clear H0 H1.
    destruct stack0; inversion H12. cbn in *.  
    apply stack_to_RTL_Incomplete_function_injective in H1; subst.
    destruct s; inversion H0; subst.
    assert (f = f0). { destruct f, f0; cbn in *; f_equal; eauto. eapply PTree.extensionality; intro p.  eapply (f_equal (fun f => f ! p)) in H7.
    repeat rewrite PTree.gmap in H7. unfold option_map in H7. repeat destruct (_ ! _); inversion H7; f_equal; eauto;
    now apply to_RTL_Incomplete_instruction_injective. } 
    subst. econstructor 5. cbn in H2. rewrite PTree.gmap in H2. unfold option_map in H2. destruct (_ ! _) ; inversion H2; f_equal; eauto. 
    destruct i; inversion H1; eauto. 
    eapply find_function_tprog'; eauto. destruct f1; cbn; eauto.
  + destruct s, s'; cbn in *; inversion H0; inversion H1; subst; clear H0 H1.
    apply stack_to_RTL_Incomplete_function_injective in H13; subst.
    econstructor 6. cbn in H2. rewrite PTree.gmap in H2. unfold option_map in H2. destruct (_ ! _) ; inversion H2; f_equal; eauto. 
    destruct i; inversion H0; eauto.
    eapply find_function_tprog'; eauto. destruct f1; cbn; eauto. destruct f0; cbn in *; eauto. 
  + destruct s, s'; cbn in *; inversion H0; inversion H1; subst; clear H0 H1.
    apply to_RTL_Incomplete_function_injective in H13. 
    apply stack_to_RTL_Incomplete_function_injective in H12; subst.
    econstructor 7. cbn in H2. rewrite PTree.gmap in H2. unfold option_map in H2. destruct (_ ! _) ; inversion H2; f_equal; eauto. 
    destruct i; inversion H0; eauto. 
    eapply eval_builtin_args_tprog'; eauto. eapply external_call_tprog'; eauto.
  + destruct s, s'; cbn in *; inversion H0; inversion H1; subst; clear H0 H1.
    apply to_RTL_Incomplete_function_injective in H13. 
    apply stack_to_RTL_Incomplete_function_injective in H12; subst.
    econstructor 8; eauto. cbn in H2. rewrite PTree.gmap in H2. unfold option_map in H2. destruct (_ ! _) ; inversion H2; f_equal; eauto. 
    destruct i; inversion H0; eauto.
  + destruct s, s'; cbn in *; inversion H0; inversion H1; subst; clear H0 H1.
    apply to_RTL_Incomplete_function_injective in H13. 
    apply stack_to_RTL_Incomplete_function_injective in H12; subst.
    econstructor 9; eauto. cbn in H2. rewrite PTree.gmap in H2. unfold option_map in H2. destruct (_ ! _) ; inversion H2; f_equal; eauto. 
    destruct i; inversion H0; eauto.
  + destruct s, s'; cbn in *; inversion H0; inversion H1; subst; clear H0 H1.
    apply stack_to_RTL_Incomplete_function_injective in H11; subst.
    econstructor 10; eauto. cbn in H2. rewrite PTree.gmap in H2. unfold option_map in H2. destruct (_ ! _) ; inversion H2; f_equal; eauto. 
    destruct i; inversion H0; eauto.
  + destruct s, s'; cbn in *; inversion H0; inversion H1; subst; clear H0 H1.
    apply stack_to_RTL_Incomplete_function_injective in H8; subst.
    destruct f0; cbn in H5; inversion H5; subst.  
    assert (f1 = f). { destruct f, f1; cbn in *; f_equal; eauto. eapply PTree.extensionality; intro p.  eapply (f_equal (fun f => f ! p)) in H4.
    repeat rewrite PTree.gmap in H4. unfold option_map in H4. repeat destruct (_ ! _); inversion H4; f_equal; eauto;
    now apply to_RTL_Incomplete_instruction_injective. } subst.  
    econstructor 11; eauto.
  + destruct s, s'; cbn in *; inversion H0; inversion H1; subst; clear H0 H1.
    apply stack_to_RTL_Incomplete_function_injective in H8; subst.
    destruct f; cbn in H5; inversion H5; subst. 
    econstructor 12; eauto. eapply external_call_tprog'; eauto.
  + destruct s, s'; cbn in *; inversion H3; inversion H1; subst; clear H1 H3.
    destruct stack; inversion H9. cbn in *.  
    apply stack_to_RTL_Incomplete_function_injective in H1; subst.
    destruct s; inversion H0; subst.
    assert (f = f0). { destruct f, f0; cbn in *; f_equal; eauto. eapply PTree.extensionality; intro p.  eapply (f_equal (fun f => f ! p)) in H5.
    repeat rewrite PTree.gmap in H5. unfold option_map in H5. repeat destruct (_ ! _); inversion H5; f_equal; eauto;
    now apply to_RTL_Incomplete_instruction_injective. } 
    subst. econstructor 13.
  Qed. 
  
Lemma function_ptr_translated_complete :
  forall (b: block) (f: RTL.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists cu tf,
  Genv.find_funct_ptr tge b = Some tf /\ AST.transf_partial_fundef (transf_function_complete (romem_for cu)) f = OK tf /\ linkorder cu prog.
Proof (Genv.find_funct_ptr_match TRANSF).
  
Lemma symbols_preserved_complete:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_match TRANSF).

Lemma sig_function_translated_complete:
  forall rm f tf,
  AST.transf_partial_fundef (transf_function_complete rm) f = OK tf ->
  funsig tf = funsig f.
Proof.
  intros. assert (AST.transf_partial_fundef (transf_function rm) f = OK (to_RTL_Incomplete_fundef tf)).
  { destruct f. monadInv H. cbn.    
    unfold transf_function_complete, transf_function_complete_obligation_1 in *.  
    set is_complete_transf_function in EQ. 
    set (i _ _ _ _) in *. clearbody i0. destruct transf_function; inversion EQ; cbn.  repeat f_equal.
    destruct f0; unfold to_RTL_Incomplete_function, map_function_; f_equal; cbn in *.
    eapply PTree.extensionality; intro p. rewrite PTree.gmap. unfold option_map.
    unfold to_RTL_function_obligation_1. destruct i0, a, a, a. cbn.  destruct to_RTL_code; cbn.
    rewrite <- e. now erewrite PTree.gmap. 
    cbn in *. destruct tf; inversion H; subst; eauto. }
  eapply sig_function_translated in H0.
  rewrite <- H0. destruct tf; cbn; eauto.
Qed.

Lemma complete_transf_initial_states :
  forall st1, initial_state prog st1 ->
  exists st2, initial_state tprog st2 /\ match_states prog transf_function_complete transf_function_complete st1 st2.
Proof.
  simpl.
  intros p H. inversion H.
  exploit function_ptr_translated_complete; eauto. intros (cu & tf & A & B & C).
  exists (Callstate nil tf nil m0); split.
  econstructor; eauto.
  eapply (Genv.init_mem_match TRANSF); eauto.
  replace (prog_main tprog) with (prog_main prog).
  rewrite symbols_preserved_complete. eauto.
  symmetry; eapply match_program_main; eauto.
  rewrite <- H3. eapply sig_function_translated_complete; eauto.
  econstructor; eauto.   
  - destruct tf; red; cbn; unfold_complete; eauto. 
  - constructor.
  - apply Mem.extends_refl.
Qed.

Lemma complete_transf_final_states : forall st1 st2 r,
  match_states prog transf_function_complete transf_function_complete st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  simpl.
  intros. inv H0. inv H. inv STACKS. inv RES. constructor.
Qed.

(* Of course this theorem can now be proven using the translation functions and properties between inductives *)
Theorem transf_program_correct:
    forward_simulation (RTL.semantics prog) (RTL.semantics tprog).
  Proof.
    intros. pose iscomplete_tprog'. apply forward_simulation_step with
      (match_states := fun s1 s2 => sound_state prog s1 /\ match_states prog transf_function_complete transf_function_complete s1 s2). 
      (* match_states prog transf_function transf_function s1 (map_state (to_RTL_Incomplete_instruction) s2)). *)
  - apply senv_preserved'. 
  - simpl; intros. exploit complete_transf_initial_states; eauto.
    intros [st2 [A B]]. pose proof (B':=B). exists st2. 
    split; eauto. split; eauto. eapply sound_initial; eauto.
  - simpl; intros. destruct H. eapply complete_transf_final_states in H0; eauto. 
  - simpl; intros. destruct H0.
    assert (sound_state prog s1') by (eapply sound_step; eauto).
    fold ge; fold tge. pose proof (H1':=H1). eapply state_to_RTL_Incomplete in H1. 
    exploit step_simulation. 5: exact H1. all: eauto. exact match_prog_tprog'. intros [st2' [A B]].
    eapply state_inversion in B as [s2' [? ?]]. 
    exists s2'. split. 2: split; eauto. rewrite H4 in A.  
    eapply step_simul; eauto.
  Qed. 

End TRANSF_PROGRAM_CORRECT.

Print Assumptions transf_program_correct.

Definition transf_program_aux (p: program) transf_f: res program :=
  transform_partial_program (AST.transf_partial_fundef (transf_f (romem_for p))) p.

Definition transf_program (p: program) : res program :=
  transf_program_aux p transf_function_complete.

Lemma transf_program_match:
  forall prog tprog, transf_program prog = OK tprog -> match_prog prog tprog.
Proof.
  intros. eapply match_transform_partial_program_contextual; eauto.
Qed.

*)

(** * ENDING OPTING-OUT *)

