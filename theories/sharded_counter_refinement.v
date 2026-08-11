From iris.algebra Require Import auth excl gmap.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import lang notation tactics.
From reloc Require Import reloc.
From reloc.lib Require Import counter lock.
From reloc.logic Require Import spec_ra spec_rules.
From summer_project Require Import sharded_counter_modular.

Set Default Proof Using "Type".

Definition msc_counter : val :=
  λ: <>,
    let: "c" := msc_new_counter #2 in
    ((λ: "k", msc_incr "c" "k"),
     (λ: <>, msc_read "c")).

Definition msc_counter2 : val :=
  λ: <>,
    let: "c" := msc_counter #() in
    (((λ: <>, (Fst "c") #0),
      (λ: <>, (Fst "c") #1)),
     Snd "c").

Definition linear_counter2 : val :=
  λ: <>,
    let: "c" := FG_counter #() in
    (((λ: <>, (Fst "c") #();; #()),
      (λ: <>, (Fst "c") #();; #())),
     Snd "c").

Definition sequential_counter2 : val :=
  λ: <>,
    let: "c" := CG_counter #() in
    (((λ: <>, (Fst "c") #();; #()),
      (λ: <>, (Fst "c") #();; #())),
     Snd "c").

Definition counter2_type : type :=
  TArrow TUnit
    (TProd
      (TProd (TArrow TUnit TUnit) (TArrow TUnit TUnit))
      (TArrow TUnit TNat)).

Section refinement.
  Context `{!relocG Σ, !mscG Σ}.

  Definition msc_refinementN : namespace := nroot .@ "msc_refinement".

  Definition msc_linear_inv (γ : msc_name) (x : loc) : iProp Σ :=
    (∃ n : nat, msc_frag γ 1%Qp n ∗ x ↦ₛ #n)%I.

  Lemma lrel_pair_intro (A B : lrel Σ) v1 v2 v1' v2' :
    A v1 v1' -∗
    B v2 v2' -∗
    (A * B)%lrel (v1, v2)%V (v1', v2')%V.
  Proof.
    iIntros "HA HB".
    iExists v1, v1', v2, v2'.
    iSplit; first done. iSplit; first done. iFrame.
  Qed.

  Lemma msc_linear_incr_refinement γ c h x :
    msc_is_counter γ c -∗
    msc_handle γ h -∗
    inv msc_refinementN (msc_linear_inv γ x) -∗
    REL msc_incr c h << (FG_increment #x;; #()) : ().
  Proof.
    iIntros "#Hcounter #Hhandle #Hinv".
    rewrite refines_eq /refines_def.
    iIntros (j) "Hj".
    iModIntro.
    wp_apply (msc_incr_spec γ c h
      (refines_right j (FG_increment #x;; #()))%I
      (λ _, refines_right j #())%I with "[] [$Hcounter $Hhandle $Hj]").
    - iIntros (total) "!# [Hauth Hj]".
      iInv msc_refinementN as (n) "[>Hfrag >Hx]" "Hclose".
      iDestruct (msc_auth_frag_agree with "Hauth Hfrag") as %->.

      iEval (rewrite /FG_increment) in "Hj".
      tp_rec j. tp_pures j. tp_load j. tp_pures j.
      tp_cmpxchg_suc j. tp_pures j.

      iMod (msc_auth_frag_update γ n n (S n)
        with "Hauth Hfrag") as "[Hauth Hfrag]".
      iMod ("Hclose" with "[Hfrag Hx]") as "_".
      { iNext. iExists (S n). iFrame.
        rewrite Nat2Z.inj_succ Z.add_comm. iFrame. }
      iModIntro. iFrame.
    - iIntros "(#Hcounter' & #Hhandle' & Hdone)".
      iDestruct "Hdone" as (total) "Hj".
      iExists #(). iFrame "Hj".
      iPureIntro. done.
  Qed.

  Lemma msc_linear_read_refinement γ c x :
    msc_is_counter γ c -∗
    inv msc_refinementN (msc_linear_inv γ x) -∗
    REL msc_read c << counter_read #x : lrel_int.
  Proof.
    iIntros "#Hcounter #Hinv".
    rewrite refines_eq /refines_def.
    iIntros (j) "Hj".
    iModIntro.
    wp_apply (msc_read_spec γ c
      (refines_right j (counter_read #x))%I
      (λ total, refines_right j #(total : nat))%I
      with "[] [$Hcounter $Hj]").
    - iIntros (total) "!# [Hauth Hj]".
      iInv msc_refinementN as (n) "[>Hfrag >Hx]" "Hclose".
      iDestruct (msc_auth_frag_agree with "Hauth Hfrag") as %->.

      iEval (rewrite /counter_read) in "Hj".
      tp_rec j. tp_pures j. tp_load j. tp_pures j.

      iMod ("Hclose" with "[Hfrag Hx]") as "_".
      { iNext. iExists n. iFrame. }
      iModIntro. iFrame.
    - iIntros (total) "[#Hcounter' Hj]".
      iExists #(total : nat). iFrame "Hj".
      iExists (Z.of_nat total). iPureIntro. done.
  Qed.

  Lemma msc_linear_counter_refinement :
    ⊢ REL msc_counter2 << linear_counter2 :
        () → ((() → ()) * (() → ())) * (() → lrel_int).
  Proof using Type*.
    rewrite /msc_counter2 /linear_counter2 /msc_counter /FG_counter.
    iApply refines_arrow_val.
    iModIntro. iIntros (v1 v2) "Hunit".
    iDestruct "Hunit" as %[-> ->].
    rel_rec_l. rel_rec_r. rel_pures_r.
    rel_alloc_r x as "Hx".
    rel_pures_r.
    rel_apply_l refines_wp_l. wp_pures.
    wp_bind (msc_new_counter #2).
    wp_apply (msc_new_counter_spec 2).
    { iPureIntro. lia. }
    iIntros (c γ) "(#Hcounter & Hhandles & Hfrag)".
    iEval (rewrite /=) in "Hhandles".
    iDestruct "Hhandles" as "(#Hhandle0 & #Hhandle1 & _)".

    iMod (inv_alloc msc_refinementN _ (msc_linear_inv γ x)
      with "[Hfrag Hx]") as "#Hinv".
    { iNext. iExists 0. iFrame. }

    wp_pures.
    iModIntro.
    iApply refines_ret. iModIntro.
    iApply lrel_pair_intro.
    - iApply lrel_pair_intro.
      + iModIntro. iIntros (u1 u2) "Hunit".
        iDestruct "Hunit" as %[-> ->].
        rel_seq_l. rel_seq_r. rel_pures_l. rel_pures_r.
        iApply (msc_linear_incr_refinement with "Hcounter Hhandle0 Hinv").
      + iModIntro. iIntros (u1 u2) "Hunit".
        iDestruct "Hunit" as %[-> ->].
        rel_seq_l. rel_seq_r. rel_pures_l. rel_pures_r.
        iApply (msc_linear_incr_refinement with "Hcounter Hhandle1 Hinv").
    - iModIntro. iIntros (u1 u2) "Hunit".
      iDestruct "Hunit" as %[-> ->].
      rel_seq_l. rel_seq_r.
      iApply (msc_linear_read_refinement with "Hcounter Hinv").
  Qed.

End refinement.

Theorem msc_linear_ctx_refinement :
  ∅ ⊨ msc_counter2 ≤ctx≤ linear_counter2 : counter2_type.
Proof.
  pose (Σ := #[relocΣ; mscΣ]).
  eapply (refines_sound Σ).
  iIntros (? Δ).
  iApply msc_linear_counter_refinement.
Qed.

Section linear_sequential_refinement.
  Context `{!relocG Σ}.

  Lemma linear_sequential_counter_refinement :
    ⊢ REL linear_counter2 << sequential_counter2 :
        () → ((() → ()) * (() → ())) * (() → lrel_int).
  Proof using Type*.
    rewrite /linear_counter2 /sequential_counter2 /FG_counter /CG_counter.
    iApply refines_arrow_val.
    iModIntro. iIntros (v1 v2) "Hunit".
    iDestruct "Hunit" as %[-> ->].
    rel_rec_l. rel_rec_r. rel_pures_r.
    rel_apply_r refines_newlock_r; auto.
    iIntros (lk) "Hlk".
    repeat rel_pure_r.
    rel_alloc_r cnt' as "Hcnt'".
    rel_pures_l. rel_alloc_l cnt as "Hcnt".

    iAssert (counter_inv lk cnt cnt') with "[Hlk Hcnt Hcnt']" as "Hinv".
    { iExists 0. by iFrame. }
    iMod (inv_alloc counterN with "[Hinv]") as "#Hinv".
    { iNext. iExact "Hinv". }

    rel_pures_r. rel_pures_l.
    iApply refines_ret. iModIntro.
    iApply lrel_pair_intro.
    - iApply lrel_pair_intro.
      + iModIntro. iIntros (u1 u2) "Hunit".
        iDestruct "Hunit" as %[-> ->].
        rel_seq_l. rel_seq_r. rel_pures_l. rel_pures_r.
        iApply (refines_seq lrel_int).
        * iApply (FG_CG_increment_refinement with "Hinv").
        * rel_values.
      + iModIntro. iIntros (u1 u2) "Hunit".
        iDestruct "Hunit" as %[-> ->].
        rel_seq_l. rel_seq_r. rel_pures_l. rel_pures_r.
        iApply (refines_seq lrel_int).
        * iApply (FG_CG_increment_refinement with "Hinv").
        * rel_values.
    - iModIntro. iIntros (u1 u2) "Hunit".
      iDestruct "Hunit" as %[-> ->]. rel_seq_l. rel_seq_r. iApply (counter_read_refinement with "Hinv").
  Qed.

End linear_sequential_refinement.


Theorem linear_sequential_ctx_refinement :
  ∅ ⊨ linear_counter2 ≤ctx≤ sequential_counter2 : counter2_type.
Proof.
  eapply (refines_sound relocΣ).
  iIntros (? Δ).
  iApply linear_sequential_counter_refinement.
Qed.

Theorem msc_sequential_ctx_refinement :
  ∅ ⊨ msc_counter2 ≤ctx≤ sequential_counter2 : counter2_type.
Proof.
  eapply (ctx_refines_transitive ∅ counter2_type
    msc_counter2 linear_counter2 sequential_counter2).
  - exact msc_linear_ctx_refinement.
  - exact linear_sequential_ctx_refinement.
Qed.

(** ReLoC only exposes a right-hand rule for one-cell allocation.  The
    sharded wrapper allocates exactly two consecutive cells, so the reverse
    refinement needs the corresponding specification-side rule. *)
Section spec_alloc2.
  Context `{!relocG Σ}.

  Lemma step_alloc2 E j K (v : val) :
    nclose specN ⊆ E →
    spec_ctx ∗ j ⤇ fill K (AllocN #2 (of_val v)) ={E}=∗
      ∃ l : loc, spec_ctx ∗ j ⤇ fill K (#l) ∗
           l ↦ₛ v ∗ (l +ₗ 1) ↦ₛ v.
  Proof.
    iIntros (HE) "[#Hspec Hj]".
    iFrame "Hspec".
    rewrite /spec_ctx tpool_pointsto_eq /tpool_pointsto_def /=.
    iDestruct "Hspec" as (ρ) "Hspec".
    iInv specN as (tp σ) ">[Hown %Hsteps]" "Hclose".
    pose (l := Loc.fresh (dom (heap σ))).
    pose (ins0 := λ h : gmap loc (option val), <[l:=Some v]> h).
    pose (ins1 := λ h : gmap loc (option val), <[l +ₗ 1:=Some v]> h).
    iCombine "Hown Hj"
      gives %[[Htp%tpool_singleton_included' _]%prod_included
               _]%auth_both_valid_discrete.
    pose proof (tpool_lookup_Some tp j
      (fill K (AllocN #2 (of_val v))) Htp) as Htp'.
    iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { by eapply auth_update, prod_local_update_1,
        singleton_local_update,
        (exclusive_local_update _ (Excl (fill K (#l)%E))). }
    iMod (own_update with "Hown") as "[Hown Hl1]".
    { eapply auth_update_alloc, prod_local_update_2, prod_local_update_2,
        (alloc_singleton_local_update _ (l +ₗ 1)
          (1%Qp, to_agree (Some v : leibnizO _))); last done.
      apply lookup_to_heap_None.
      apply not_elem_of_dom_1.
      unfold l.
      apply Loc.fresh_fresh. lia. }
    iMod (own_update with "Hown") as "[Hown Hl0]".
    { eapply auth_update_alloc, prod_local_update_2, prod_local_update_2,
        (alloc_singleton_local_update _ l
          (1%Qp, to_agree (Some v : leibnizO _))); last done.
      rewrite lookup_insert_ne.
      - apply lookup_to_heap_None.
        apply not_elem_of_dom_1.
        unfold l.
        rewrite -{1}(Loc.add_0 (Loc.fresh (dom (heap σ)))).
        apply Loc.fresh_fresh. lia.
      - intros Heq. apply Loc.eq_spec in Heq. simpl in Heq. lia. }
    rewrite !heapS_pointsto_eq /heapS_pointsto_def /=.
    iExists l. iFrame "Hj Hl0 Hl1".
    iApply "Hclose". iNext.
    iExists (<[j:=fill K (#l)]> tp),
      (state_upd_heap ins0 (state_upd_heap ins1 σ)).
    rewrite /to_state !to_heap_insert to_tpool_insert'; last eauto.
    iFrame "Hown".
    iPureIntro.
    eapply rtc_r.
    - exact Hsteps.
    - eapply step_insert_no_fork.
      + exact Htp'.
      + replace
          (state_upd_heap ins0 (state_upd_heap ins1 σ))
          with (state_init_heap l 2 v σ).
        * apply alloc_fresh. lia.
        * destruct σ as [h ps]. unfold ins0, ins1.
          rewrite /state_init_heap /= /heap_array /=.
          f_equal. rewrite -assoc_L.
          rewrite right_id. by rewrite !insert_union_singleton_l.
  Qed.

  Lemma refines_alloc2_r E (K : list ectx_item) (t : expr)
      (v : val) (A : lrel Σ) :
    nclose specN ⊆ E →
    (∀ l, l ↦ₛ v -∗ (l +ₗ 1) ↦ₛ v -∗
      REL t << fill K (#l) @ E : A) -∗
    REL t << fill K (AllocN #2 (of_val v)) @ E : A.
  Proof.
    iIntros (HE) "Hcont".
    iApply refines_step_r.
    iIntros (j) "Hj".
    iMod (step_alloc2 with "Hj") as (l) "($ & Hj & Hl0 & Hl1)"; first done.
    iModIntro. iExists #l. iFrame "Hj".
    iApply ("Hcont" with "Hl0 Hl1").
  Qed.
End spec_alloc2.

Section linear_msc_reverse.
  Context `{!relocG Σ}.

  Definition linear_msc_reverseN : namespace :=
    nroot .@ "linear_msc_reverse".

  Definition linear_msc_reverse_inv (x a : loc) : iProp Σ :=
    (∃ n0 n1 : nat,
      x ↦ #((n0 + n1)%nat) ∗ a ↦ₛ #n0 ∗ (a +ₗ 1) ↦ₛ #n1)%I.

  Definition linear_msc_reverse_state (a : loc) (n : nat) : iProp Σ :=
    (∃ n0 n1 : nat,
      ⌜n = (n0 + n1)%nat⌝ ∗ a ↦ₛ #n0 ∗ (a +ₗ 1) ↦ₛ #n1)%I.

  Lemma linear_msc_incr0_refinement x a :
    inv linear_msc_reverseN (linear_msc_reverse_inv x a) -∗
    REL (FG_increment #x;; #()) << msc_incr (#a, #2)%V #0 : ().
  Proof.
    iIntros "#Hinv".
    rel_apply_l
      (FG_increment_atomic_l (linear_msc_reverse_state a) True%I);
      first done.
    iModIntro.
    iInv linear_msc_reverseN as (n0 n1) "(>Hx & >Ha0 & >Ha1)" "Hclose".
    iModIntro.
    iExists (n0 + n1)%nat. iFrame "Hx".
    iSplitL "Ha0 Ha1".
    { iExists n0, n1. iFrame. done. }
    iSplit.
    - iIntros "(Hx & Hstate)".
      iDestruct "Hstate" as (m0 m1 ->) "(Ha0 & Ha1)".
      iApply "Hclose". iNext. iExists m0, m1. iFrame.
    - iIntros "(Hx & Hstate) _".
      iDestruct "Hstate" as (m0 m1 ->) "(Ha0 & Ha1)".
      rewrite /msc_incr.
      rel_pures_r. rewrite Loc.add_0.
      rel_apply_r (refines_faa_r _ _ _ _ (Z.of_nat m0) 1 _ _ with "Ha0").
      iIntros "Ha0".
      iMod ("Hclose" with "[Hx Ha0 Ha1]") as "_".
      { iNext. iExists (m0 + 1)%nat, m1.
        replace (m0 + 1 + m1)%nat with (m0 + m1 + 1)%nat by lia.
        rewrite !Nat2Z.inj_add /=.
        iFrame. }
      rel_pures_r. rel_pures_l. rel_values.
  Qed.

  Lemma linear_msc_incr1_refinement x a :
    inv linear_msc_reverseN (linear_msc_reverse_inv x a) -∗
    REL (FG_increment #x;; #()) << msc_incr (#a, #2)%V #1 : ().
  Proof.
    iIntros "#Hinv".
    rel_apply_l
      (FG_increment_atomic_l (linear_msc_reverse_state a) True%I);
      first done.
    iModIntro.
    iInv linear_msc_reverseN as (n0 n1) "(>Hx & >Ha0 & >Ha1)" "Hclose".
    iModIntro.
    iExists (n0 + n1)%nat. iFrame "Hx".
    iSplitL "Ha0 Ha1".
    { iExists n0, n1. iFrame. done. }
    iSplit.
    - iIntros "(Hx & Hstate)".
      iDestruct "Hstate" as (m0 m1 ->) "(Ha0 & Ha1)".
      iApply "Hclose". iNext. iExists m0, m1. iFrame.
    - iIntros "(Hx & Hstate) _".
      iDestruct "Hstate" as (m0 m1 ->) "(Ha0 & Ha1)".
      rewrite /msc_incr.
      rel_pures_r.
      rel_apply_r (refines_faa_r _ _ _ _ (Z.of_nat m1) 1 _ _ with "Ha1").
      iIntros "Ha1".
      iMod ("Hclose" with "[Hx Ha0 Ha1]") as "_".
      { iNext. iExists m0, (m1 + 1)%nat.
        replace (m0 + (m1 + 1))%nat with (m0 + m1 + 1)%nat by lia. rewrite !Nat2Z.inj_add /=.
        iFrame. }
      rel_pures_r. rel_pures_l. rel_values.
  Qed.

  Lemma linear_msc_read_refinement x a :
    inv linear_msc_reverseN (linear_msc_reverse_inv x a) -∗
    REL counter_read #x << msc_read (#a, #2)%V : lrel_int.
  Proof.
    iIntros "#Hinv".
    rel_apply_l
      (counter_read_atomic_l (linear_msc_reverse_state a) True%I);
      first done.
    iModIntro.
    iInv linear_msc_reverseN as (n0 n1) "(>Hx & >Ha0 & >Ha1)" "Hclose".
    iModIntro.
    iExists (n0 + n1)%nat. iFrame "Hx".
    iSplitL "Ha0 Ha1".
    { iExists n0, n1. iFrame. done. }
    iSplit.
    - iIntros "(Hx & Hstate)".
      iDestruct "Hstate" as (m0 m1 ->) "(Ha0 & Ha1)".
      iApply "Hclose". iNext. iExists m0, m1. iFrame.
    - iIntros "(Hx & Hstate) _".
      iDestruct "Hstate" as (m0 m1 ->) "(Ha0 & Ha1)".
      rewrite /msc_read.
      rel_pures_r.
      rel_newproph_r p as "#Hp".
      rel_pures_r. rewrite /msc_sum_loop. rel_pures_r. rewrite Loc.add_0. rel_load_r. rel_pures_r. rel_load_r. rel_pures_r.
      iMod ("Hclose" with "[Hx Ha0 Ha1]") as "_".
      { iNext. iExists m0, m1. iFrame. }
      rel_resolveproph_r.
      rel_pures_r.
      rel_values.
      iExists (Z.of_nat (m0 + m1)). iPureIntro. split; first done. f_equal; try reflexivity. rewrite Nat2Z.inj_add. simpl. reflexivity.
  Qed.

  Lemma linear_msc_counter_refinement :
    ⊢ REL linear_counter2 << msc_counter2 :
        () → ((() → ()) * (() → ())) * (() → lrel_int).
  Proof using Type*.
    rewrite /linear_counter2 /msc_counter2 /FG_counter /msc_counter.
    iApply refines_arrow_val.
    iModIntro. iIntros (v1 v2) "Hunit".
    iDestruct "Hunit" as %[-> ->].
    rel_rec_l. rel_rec_r. rel_pures_l. rel_pures_r.
    rel_alloc_l x as "Hx".
    rel_pures_l.
    rewrite /msc_new_counter.
    rel_pures_r.
    rel_apply_r refines_alloc2_r; first auto.
    iIntros (a) "Ha0 Ha1".
    rel_pures_r.
    iMod (inv_alloc linear_msc_reverseN _ (linear_msc_reverse_inv x a)
      with "[Hx Ha0 Ha1]") as "#Hinv".
    { iNext. iExists 0%nat, 0%nat. iFrame. }
    iApply refines_ret. iModIntro.
    iApply lrel_pair_intro.
    - iApply lrel_pair_intro.
      + iModIntro. iIntros (u1 u2) "Hunit".
        iDestruct "Hunit" as %[-> ->].
        rel_seq_l. rel_seq_r. rel_pures_l. rel_pures_r.
        iApply (linear_msc_incr0_refinement with "Hinv").
      + iModIntro. iIntros (u1 u2) "Hunit".
        iDestruct "Hunit" as %[-> ->].
        rel_seq_l. rel_seq_r. rel_pures_l. rel_pures_r.
        iApply (linear_msc_incr1_refinement with "Hinv").
    - iModIntro. iIntros (u1 u2) "Hunit".
      iDestruct "Hunit" as %[-> ->].
      rel_seq_l. rel_seq_r.
      iApply (linear_msc_read_refinement with "Hinv").
  Qed.
End linear_msc_reverse.

Theorem linear_msc_ctx_refinement :
  ∅ ⊨ linear_counter2 ≤ctx≤ msc_counter2 : counter2_type.
Proof.
  eapply (refines_sound relocΣ).
  iIntros (? Δ).
  iApply linear_msc_counter_refinement.
Qed.

Section sequential_linear_reverse.
  Context `{!relocG Σ, !lockG Σ}.

  Definition sequential_linear_lockN : namespace :=
    nroot .@ "sequential_linear_lock".
  Definition sequential_linear_counterN : namespace :=
    nroot .@ "sequential_linear_counter".

  Definition sequential_linear_lock_res (x : loc) : iProp Σ :=
    (∃ z : Z, x ↦{#1/2} #z)%I.

  Definition sequential_linear_inv (x y : loc) : iProp Σ :=
    (∃ z : Z, x ↦{#1/2} #z ∗ y ↦ₛ #z)%I.

  Lemma FG_increment_Z_r K E t A (y : loc) (z : Z) :
    nclose specN ⊆ E →
    y ↦ₛ #z -∗
    (y ↦ₛ #(1 + z) -∗
      REL t << fill K (of_val #z) @ E : A) -∗
    REL t << fill K (FG_increment #y) @ E : A.
  Proof.
    iIntros (?) "Hy Hcont".
    rewrite /FG_increment.
    rel_rec_r. repeat rel_pure_r.
    rel_load_r. repeat rel_pure_r.
    rel_cmpxchg_suc_r. rel_pures_r.
    by iApply ("Hcont" with "Hy").
  Qed.

  Lemma sequential_linear_incr_refinement γ lk x y :
    is_lock sequential_linear_lockN γ #lk (sequential_linear_lock_res x) -∗
    inv sequential_linear_counterN (sequential_linear_inv x y) -∗
    REL (CG_increment #x #lk;; #()) << (FG_increment #y;; #()) : ().
  Proof.
    iIntros "#Hlock #Hinv".
    rewrite /CG_increment.
    rel_pures_l.
    rel_apply_l (refines_acquire_l sequential_linear_lockN
      (sequential_linear_lock_res x) with "Hlock").
    iNext. iIntros "Hlocked Hres".
    iDestruct "Hres" as (n) "Hx".
    rel_pures_l. rel_load_l. rel_pures_l.
    rel_store_l_atomic.
    iInv sequential_linear_counterN as (m) "(>Hx' & >Hy)" "Hclose".
    iDestruct (pointsto_agree with "Hx Hx'") as %Heq.
    simplify_eq.
    iCombine "Hx Hx'" as "Hx".
    iModIntro. iExists _. iFrame "Hx". iNext.
    iIntros "Hx".
    rel_apply_r (FG_increment_Z_r with "Hy").
    iIntros "Hy".
    iDestruct "Hx" as "[Hx Hx']".
    iMod ("Hclose" with "[Hx' Hy]") as "_".
    { iNext. iExists (1 + m)%Z. iFrame. }
    rel_pures_l.
    rel_apply_l (refines_release_l sequential_linear_lockN
      (sequential_linear_lock_res x) with "Hlock Hlocked [Hx]").
    { iExists (1 + m)%Z. iFrame. }
    iNext.
    rel_pures_l. rel_pures_r. rel_values.
  Qed.

  Lemma sequential_linear_read_refinement x y :
    inv sequential_linear_counterN (sequential_linear_inv x y) -∗
    REL counter_read #x << counter_read #y : lrel_int.
  Proof.
    iIntros "#Hinv".
    rewrite /counter_read.
    rel_pures_l.
    rel_load_l_atomic.
    iInv sequential_linear_counterN as (z) "(>Hx & >Hy)" "Hclose".
    iModIntro. iExists #z. iFrame "Hx". iNext.
    iIntros "Hx".
    rel_load_r.
    iMod ("Hclose" with "[Hx Hy]") as "_".
    { iNext. iExists z. iFrame. }
    rel_values.

  Qed.

  Lemma sequential_linear_counter_refinement :
    ⊢ REL sequential_counter2 << linear_counter2 :
        () → ((() → ()) * (() → ())) * (() → lrel_int).
  Proof using Type*.
    rewrite /sequential_counter2 /linear_counter2 /CG_counter /FG_counter.
    iApply refines_arrow_val.
    iModIntro. iIntros (v1 v2) "Hunit".
    iDestruct "Hunit" as %[-> ->].
    rel_rec_l. rel_rec_r. rewrite /newlock. rel_pures_l. rel_pures_r.

    rel_pures_l. rel_alloc_l lk as "Hlk". rel_pures_l. rel_alloc_l x as "Hx". rel_pures_l. rel_alloc_r y as "Hy". rel_pures_r.
    iDestruct "Hx" as "[HxL HxG]".
    iMod (own_alloc (Excl ())) as (γ) "Hγ"; first done.
    iMod (inv_alloc sequential_linear_lockN _
      (lock_inv γ lk (sequential_linear_lock_res x))
      with "[Hlk Hγ HxL]") as "#Hlock_inv".
    { iNext. iExists false. iFrame. }
    iAssert (is_lock sequential_linear_lockN γ #lk
      (sequential_linear_lock_res x)) as "#Hlock".
    { iExists lk. iSplit; first done. iExact "Hlock_inv". }
    iMod (inv_alloc sequential_linear_counterN _
      (sequential_linear_inv x y) with "[HxG Hy]") as "#Hinv".
    { iNext. iExists 0%Z. iFrame. }
    iApply refines_ret. iModIntro.
    iApply lrel_pair_intro.
    - iApply lrel_pair_intro.
      + iModIntro. iIntros (u1 u2) "Hunit".
        iDestruct "Hunit" as %[-> ->].
        rel_seq_l. rel_seq_r. rel_pures_l. rel_pures_r.
        iApply (sequential_linear_incr_refinement with "Hlock Hinv").
      + iModIntro. iIntros (u1 u2) "Hunit".
        iDestruct "Hunit" as %[-> ->].
        rel_seq_l. rel_seq_r. rel_pures_l. rel_pures_r.
        iApply (sequential_linear_incr_refinement with "Hlock Hinv").
    - iModIntro. iIntros (u1 u2) "Hunit".
      iDestruct "Hunit" as %[-> ->].
      rel_seq_l. rel_seq_r.
      iApply (sequential_linear_read_refinement with "Hinv").
  Qed.
End sequential_linear_reverse.

Theorem sequential_linear_ctx_refinement :
  ∅ ⊨ sequential_counter2 ≤ctx≤ linear_counter2 : counter2_type.
Proof.
  pose (Σ := #[relocΣ; lockΣ]).
  eapply (refines_sound Σ).
  iIntros (? Δ).
  iApply sequential_linear_counter_refinement.
Qed.

Theorem sequential_msc_ctx_refinement :
  ∅ ⊨ sequential_counter2 ≤ctx≤ msc_counter2 : counter2_type.
Proof.
  eapply (ctx_refines_transitive ∅ counter2_type
    sequential_counter2 linear_counter2 msc_counter2).
  - exact sequential_linear_ctx_refinement.
  - exact linear_msc_ctx_refinement.
Qed.

Theorem msc_linear_ctx_equiv :
  ∅ ⊨ msc_counter2 =ctx= linear_counter2 : counter2_type.
Proof.
  split.
  - exact msc_linear_ctx_refinement.
  - exact linear_msc_ctx_refinement.
Qed.

Theorem linear_sequential_ctx_equiv :
  ∅ ⊨ linear_counter2 =ctx= sequential_counter2 : counter2_type.
Proof.
  split.
  - exact linear_sequential_ctx_refinement.
  - exact sequential_linear_ctx_refinement.
Qed.

Theorem msc_sequential_ctx_equiv :
  ∅ ⊨ msc_counter2 =ctx= sequential_counter2 : counter2_type.
Proof.
  split.
  - exact msc_sequential_ctx_refinement.
  - exact sequential_msc_ctx_refinement.
Qed.
