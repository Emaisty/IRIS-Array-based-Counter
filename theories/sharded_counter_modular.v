From iris.algebra Require Import agree frac.
From iris.algebra.lib Require Import frac_auth.
From iris.base_logic.lib Require Import ghost_map invariants mono_nat saved_prop.
From iris.bi.lib Require Import fractional.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import par.
From iris.prelude Require Import options.

From summer_project Require Import counter_spec_modular.

Definition msc_new_counter : val :=
  λ: "T", (AllocN "T" #0, "T").

Definition msc_incr : val :=
  λ: "c" "k",
    let: "l" := (Fst "c") +ₗ "k" in
    FAA "l" #1;;
    #().

Definition msc_sum_loop : val :=
  rec: "sum" "a" "T" "i" "acc" :=
    if: "i" = "T" then "acc"
    else
      let: "n" := ! ("a" +ₗ "i") in
      "sum" "a" "T" ("i" + #1) ("acc" + "n").

Definition msc_read : val :=
  λ: "c",
    let: "p" := NewProph in
    let: "a" := Fst "c" in
    let: "T" := Snd "c" in
    let: "r" := msc_sum_loop "a" "T" #0 #0 in
    ResolveProph "p" "r";;
    "r".

Definition msc_proph_total (pvs : list (val * val)) : nat :=
  match pvs with
  | (_, LitV (LitInt z)) :: _ => Z.to_nat z
  | _ => 0
  end.

Lemma msc_proph_total_cons (r : nat) (pvs : list (val * val)) :
  msc_proph_total ((#(), #(r : nat)) :: pvs) = r.
Proof.
  simpl. by rewrite Nat2Z.id.
Qed.

Definition msc_modelR : cmra := frac_authR (agreeR natO).

Class mscG Σ := MSCG {
  msc_modelG :: inG Σ msc_modelR;
  msc_mono_natG :: mono_natG Σ;
  msc_request_mapG :: ghost_mapG Σ nat (nat * gname);
  msc_saved_predG :: savedPredG Σ natO;
}.

Definition mscΣ : gFunctors :=
  #[GFunctor msc_modelR;
    mono_natΣ;
    ghost_mapΣ nat (nat * gname);
    savedPredΣ natO].

Global Instance subG_mscΣ Σ : subG mscΣ Σ → mscG Σ.
Proof.
  solve_inG.
Qed.

Definition mscN : namespace := nroot .@ "sharded_counter_modular".
Definition mscE : coPset := ⊤.
Lemma mscN_subset_mscE : ↑mscN ⊆ mscE.
Proof.
  set_solver.
Qed.


Definition msc_auth_elem (n : nat) : msc_modelR :=
  ●F (to_agree n).
Definition msc_frag_elem (q : Qp) (n : nat) : msc_modelR :=
  ◯F{q} (to_agree n).
Typeclasses Opaque msc_auth_elem msc_frag_elem.


Section model.
  Context `{!mscG Σ}.

  Global Instance msc_frag_elem_fractional γ n :
    Fractional (λ q, own γ (msc_frag_elem q n))%I.
  Proof.
    intros p q. rewrite /msc_frag_elem -own_op.
    f_equiv. by rewrite -frac_auth_frag_op agree_idemp.
  Qed.

  Global Instance msc_frag_elem_as_fractional γ q n :
    AsFractional (own γ (msc_frag_elem q n))
      (λ q, own γ (msc_frag_elem q n))%I q.
  Proof.
    split; first done. apply _.
  Qed.
End model.


Section proof.
  Context `{!heapGS Σ, !mscG Σ}.
  Record msc_name := MscName {
    msc_model_name : gname;
    msc_size : nat;
    msc_shard_names : list gname;
    msc_request_name : gname;
  }.



  Definition msc_auth (γ : msc_name) (n : nat) : iProp Σ :=
    own γ.(msc_model_name) (msc_auth_elem n).
  Definition msc_frag
      (γ : msc_name) (q : Qp) (n : nat) : iProp Σ :=
    own γ.(msc_model_name) (msc_frag_elem q n).
  Global Instance msc_frag_fractional γ n :
    Fractional (λ q, msc_frag γ q n).
  Proof.
    apply _.
  Qed.



  Lemma msc_auth_frag_update γ n m k :
    msc_auth γ n -∗ msc_frag γ 1%Qp m ==∗
    msc_auth γ k ∗ msc_frag γ 1%Qp k.
  Proof.
    iIntros "Hauth Hfrag".
    iMod (own_update_2 _ _ _
      (msc_auth_elem k ⋅ msc_frag_elem 1%Qp k)
      with "Hauth Hfrag") as "H".
    { rewrite /msc_auth_elem /msc_frag_elem.
      apply frac_auth_update_1. done. }
    iEval (rewrite own_op) in "H".
    iExact "H".
  Qed.



  Definition msc_shard_auth
      (a : loc) (i n : nat) (γs : gname) : iProp Σ :=
    (a +ₗ i) ↦ #(n : nat) ∗ mono_nat_auth_own γs 1 n.

  Definition msc_shard_lb (γs : gname) (n : nat) : iProp Σ :=
    mono_nat_lb_own γs n.




  Definition msc_read_pending
      (γ : msc_name) (total r : nat) (γQ : gname) : iProp Σ :=
    ∃ (P : iProp Σ) (Q : nat → iProp Σ),
      saved_pred_own γQ DfracDiscarded Q ∗
      P ∗
      □ (msc_auth γ r ∗ P
          ={mscE ∖ ↑mscN}=∗
         msc_auth γ r ∗ Q r) ∗
      ⌜total < r⌝.

  Definition msc_read_done
      (total r : nat) (γQ : gname) : iProp Σ :=
    ∃ Q : nat → iProp Σ,
      saved_pred_own γQ DfracDiscarded Q ∗ Q r ∗ ⌜r ≤ total⌝.



  Definition msc_read_state
      (γ : msc_name) (total : nat) (request : nat * gname) : iProp Σ :=
    msc_read_pending γ total request.1 request.2 ∨
    msc_read_done total request.1 request.2.
  Definition msc_requests
      (γ : msc_name) (total : nat)
      (requests : gmap nat (nat * gname)) : iProp Σ :=
    ghost_map_auth γ.(msc_request_name) 1 requests ∗
    [∗ map] _ ↦ request ∈ requests, msc_read_state γ total request.



  Definition msc_shards
      (a : loc) (ns : list nat) (γs : list gname) : iProp Σ :=
    ([∗ list] i ↦ n ∈ ns, (a +ₗ i) ↦ #(n : nat)) ∗
    [∗ list] _ ↦ n; γi ∈ ns; γs, mono_nat_auth_own γi 1 n.

  Definition msc_lbs (ns : list nat) (γs : list gname) : iProp Σ :=
    [∗ list] _ ↦ n; γi ∈ ns; γs, msc_shard_lb γi n.

  Global Instance msc_lbs_persistent ns γs :
    Persistent (msc_lbs ns γs).
  Proof.
    apply _.
  Qed.


  Lemma msc_read_state_advance γ n request :
    msc_auth γ (S n) -∗
    msc_read_state γ n request
      ={mscE ∖ ↑mscN}=∗
    msc_auth γ (S n) ∗ msc_read_state γ (S n) request.
  Proof.
    destruct request as [r γQ].
    rewrite /msc_read_state /msc_read_pending /msc_read_done /=.
    iIntros "Hauth [Hpending | Hdone]".
    - iDestruct "Hpending" as (P Q) "(#HQsaved & HP & #HVS & %Hnr)".
      destruct (decide (r = S n)) as [->|Hne].
      + iMod ("HVS" with "[$Hauth $HP]") as "[Hauth HQ]".
        iModIntro. iFrame "Hauth". iRight.
        iExists Q. iFrame "HQ HQsaved". iPureIntro. lia.
      + iModIntro. iFrame "Hauth". iLeft.
        iExists P, Q. iFrame "HQsaved HP HVS". iPureIntro. lia.
    - iDestruct "Hdone" as (Q) "(#HQsaved & HQ & %Hrn)".
      iModIntro. iFrame "Hauth". iRight.
      iExists Q. iFrame "HQ HQsaved". iPureIntro. lia.
  Qed.

  Lemma msc_read_states_advance γ n
      (requests : gmap nat (nat * gname)) :
    msc_auth γ (S n) -∗
    ([∗ map] _ ↦ request ∈ requests, msc_read_state γ n request)
      ={mscE ∖ ↑mscN}=∗
    msc_auth γ (S n) ∗
    [∗ map] _ ↦ request ∈ requests, msc_read_state γ (S n) request.
  Proof.
    induction requests as [|k request requests Hnone IH] using map_ind.
    - rewrite !big_sepM_empty. iIntros "Hauth _".
      iModIntro. iFrame.
    - rewrite !big_sepM_insert //.
      iIntros "Hauth [Hrequest Hrequests]".
      iMod (IH with "Hauth Hrequests") as "[Hauth Hrequests]".
      iMod (msc_read_state_advance with "Hauth Hrequest")
        as "[Hauth Hrequest]".
      iModIntro. iFrame.
  Qed.

  Lemma msc_requests_advance γ n requests :
    msc_auth γ (S n) -∗ msc_requests γ n requests
      ={mscE ∖ ↑mscN}=∗
    msc_auth γ (S n) ∗ msc_requests γ (S n) requests.
  Proof.
    iIntros "Hauth [Hmap Hstates]".
    iMod (msc_read_states_advance with "Hauth Hstates")
      as "[$ Hstates]".
    iModIntro. iFrame.
  Qed.

  Lemma msc_request_register γ total r γQ requests
      (P : iProp Σ) (Q : nat → iProp Σ) :
    total ≤ r →
    saved_pred_own γQ DfracDiscarded Q -∗
    □ (msc_auth γ r ∗ P
        ={mscE ∖ ↑mscN}=∗
       msc_auth γ r ∗ Q r) -∗
    msc_auth γ total -∗ msc_requests γ total requests -∗ P
      ={mscE ∖ ↑mscN}=∗
    ∃ id : nat,
      msc_auth γ total ∗
      msc_requests γ total (<[id := (r, γQ)]> requests) ∗
      id ↪[γ.(msc_request_name)] (r, γQ).
  Proof.
    iIntros (Htotalr) "#HQsaved #HVS Hauth [Hmap Hstates] HP".
    set (id := fresh (dom requests)).
    have Hid : requests !! id = None.
    { apply not_elem_of_dom. apply is_fresh. }
    destruct (decide (total = r)) as [->|Hne].
    - iMod ("HVS" with "[$Hauth $HP]") as "[Hauth HQ]".
      iAssert (msc_read_state γ r (r, γQ))
        with "[HQ]" as "Hstate".
      { rewrite /msc_read_state /msc_read_done /=. iRight.
        iExists Q. iFrame "HQ HQsaved". iPureIntro. lia. }
      iMod (ghost_map_insert id (r, γQ) with "Hmap")
        as "[Hmap Hid]"; first done.
      iModIntro. iExists id. iFrame "Hauth Hid".
      rewrite /msc_requests big_sepM_insert //; iFrame.
    - iAssert (msc_read_state γ total (r, γQ))
        with "[HP]" as "Hstate".
      { rewrite /msc_read_state /msc_read_pending /=. iLeft.
        iExists P, Q. iFrame "HP HQsaved HVS". iPureIntro. lia. }
      iMod (ghost_map_insert id (r, γQ) with "Hmap")
        as "[Hmap Hid]"; first done.
      iModIntro. iExists id. iFrame "Hauth Hid".
      rewrite /msc_requests big_sepM_insert //; iFrame.
  Qed.

  Lemma msc_request_take γ total r γQ id requests
      (Q : nat → iProp Σ) :
    r ≤ total →
    saved_pred_own γQ DfracDiscarded Q -∗
    id ↪[γ.(msc_request_name)] (r, γQ) -∗
    msc_requests γ total requests ==∗
    msc_requests γ total (delete id requests) ∗ ▷ Q r.
  Proof.
    iIntros (Hrtotal) "#HQsaved Hid [Hmap Hstates]".
    iDestruct (ghost_map_lookup with "Hmap Hid") as %Hlookup.
    iEval (rewrite (big_sepM_delete _ requests id (r, γQ) Hlookup))
      in "Hstates".
    iDestruct "Hstates" as "[Hstate Hstates]".
    iEval (rewrite /msc_read_state /msc_read_pending /msc_read_done /=)
      in "Hstate".
    iDestruct "Hstate" as "[Hpending | Hdone]".
    - iDestruct "Hpending" as (P Q') "(_ & _ & _ & %Hlt)".
      exfalso. lia.
    - iDestruct "Hdone" as (Q') "(#HQsaved' & HQ' & _)".
      iPoseProof (saved_pred_agree _ _ _ _ _ r
        with "HQsaved HQsaved'") as "Heq".
      iAssert (▷ Q r)%I with "[HQ' Heq]" as "HQ".
      { iNext. iRewrite "Heq". iExact "HQ'". }
      iMod (ghost_map_delete with "Hmap Hid") as "Hmap".
      iModIntro. iFrame "HQ".
      rewrite /msc_requests. iFrame.
  Qed.

  Lemma msc_mono_alloc_zeros T :
    ⊢ |==> ∃ γs : list gname,
      ⌜length γs = T⌝ ∗
      [∗ list] γi ∈ γs, mono_nat_auth_own γi 1 0.
  Proof.
    (* Induct on the requested number of ghost names. *)
    induction T as [|T IH].
    (* Zero shards require no allocations. *)
    - iModIntro. iExists []. simpl. auto.
    (* Prepend one fresh zero authority to the recursively allocated list. *)
    - iMod IH as (γs) "[%Hlen Hγs]".
      iMod (mono_nat_own_alloc 0) as (γi) "[Hγi _]".
      iModIntro. iExists (γi :: γs). simpl.
      iFrame. iPureIntro. lia.
  Qed.






  Definition msc_inv (γ : msc_name) (a : loc) : iProp Σ :=
    ∃ (ns : list nat) (requests : gmap nat (nat * gname)),
      ⌜length ns = γ.(msc_size)⌝ ∗
      ⌜length γ.(msc_shard_names) = γ.(msc_size)⌝ ∗
      msc_auth γ (sum_list ns) ∗
      msc_shards a ns γ.(msc_shard_names) ∗
      msc_requests γ (sum_list ns) requests.

  Definition msc_is_counter
      (γ : msc_name) (c : val) : iProp Σ :=
    ∃ a : loc,
      ⌜c = (#a, #(γ.(msc_size) : nat))%V⌝ ∗
      inv mscN (msc_inv γ a).

  Global Instance msc_is_counter_persistent γ c :
    Persistent (msc_is_counter γ c).
  Proof.
    apply _.
  Qed.

  Definition msc_handle (γ : msc_name) (h : val) : iProp Σ :=
    ∃ i : nat, ⌜h = #(i : nat)⌝ ∗ ⌜i < γ.(msc_size)⌝.

  Global Instance msc_handle_persistent γ h :
    Persistent (msc_handle γ h).
  Proof.
    apply _.
  Qed.




  Lemma msc_make_handles γ :
    ⊢ [∗ list] i ∈ seq 0 γ.(msc_size), msc_handle γ #(i : nat).
  Proof.
    iApply big_sepL_intro.
    iIntros "!>" (k i Hlookup).
    apply lookup_seq in Hlookup as [-> Hk]. simpl.
    rewrite /msc_handle.
    iExists k. iPureIntro. split; first done. exact Hk.
  Qed.

  Lemma msc_sum_list_insert_S ns i n :
    ns !! i = Some n →
    sum_list (<[i := S n]> ns) = S (sum_list ns).
  Proof.
    revert i. induction ns as [|m ns IH]; intros [|i] Hlookup;
      simpl in Hlookup |- *; simplify_eq; first lia.
    rewrite (IH i Hlookup). lia.
  Qed.




  Lemma msc_load_shard γ a (i : nat) γi n0 :
    γ.(msc_shard_names) !! i = Some γi →
    {{{ inv mscN (msc_inv γ a) ∗ msc_shard_lb γi n0 }}}
      ! #(a +ₗ i) @ mscE
    {{{ (n : nat), RET #(n : nat);
        msc_shard_lb γi n ∗ ⌜n0 ≤ n⌝ }}}.
  Proof.
    iIntros (Hγi Φ) "[#Hinv #Hn0] HΦ".
    iInv mscN as (ns requests)
      "(>%Hlen & >%Hγlen & >Hauth & >Hshards & Hrequests)" "Hclose".
    iDestruct "Hshards" as "[Hcells Hmonos]".
    have Hi_ns : i < length ns.
    { have Hi_γs := lookup_lt_Some _ _ _ Hγi. lia. }
    destruct (lookup_lt_is_Some_2 ns i Hi_ns) as [n Hn].
    iDestruct (big_sepL_insert_acc _ _ _ _ Hn with "Hcells")
      as "[Hl Hcells]".
    iDestruct (big_sepL2_lookup_acc _ _ _ i n γi Hn Hγi with "Hmonos")
      as "[Hmono Hmonos]".
    iDestruct (mono_nat_lb_own_valid with "Hmono Hn0") as %[_ Hn0n].
    iPoseProof (mono_nat_lb_own_get with "Hmono") as "#Hn".
    wp_load.
    iDestruct ("Hcells" $! n with "Hl") as "Hcells".
    iEval (rewrite (list_insert_id _ _ _ Hn)) in "Hcells".
    iDestruct ("Hmonos" with "Hmono") as "Hmonos".
    iMod ("Hclose" with "[Hauth Hcells Hmonos Hrequests]") as "_".
    { iNext. iExists ns, requests.
      iSplit; first done.
      iSplit; first done.
      iSplitL "Hauth"; first done.
      iSplitL "Hcells Hmonos".
      { rewrite /msc_shards. iSplitL "Hcells".
        - iExact "Hcells".
        - iExact "Hmonos". }
      iExact "Hrequests". }
    iModIntro. iApply ("HΦ" $! n). iFrame "Hn". done.
  Qed.

  Lemma msc_monos_snapshot ns γs :
    ([∗ list] _ ↦ n; γi ∈ ns; γs, mono_nat_auth_own γi 1 n) -∗
    ([∗ list] _ ↦ n; γi ∈ ns; γs, mono_nat_auth_own γi 1 n) ∗
    msc_lbs ns γs.
  Proof.
    iIntros "Hmonos".
    iPoseProof (big_sepL2_mono with "Hmonos") as "#Hlbs".
    { iIntros (i n γi Hn Hγi) "Hmono".
      iApply mono_nat_lb_own_get. iExact "Hmono". }
    iFrame "Hmonos Hlbs".
  Qed.

  Lemma msc_sum_loop_bounds γ a
      (T i acc : nat) (lower : list nat) :
    length lower = T →
    length γ.(msc_shard_names) = T →
    i ≤ T →
    {{{ inv mscN (msc_inv γ a) ∗
        msc_lbs lower γ.(msc_shard_names) }}}
      msc_sum_loop #a #T #(i : nat) #(acc : nat) @ mscE
    {{{ (r : nat), RET #(r : nat);
        ∃ read_values : list nat,
          ⌜length read_values = T - i⌝ ∗
          ⌜r = (acc + sum_list read_values)%nat⌝ ∗
          ⌜(sum_list (drop i lower) ≤ sum_list read_values)%nat⌝ ∗
          msc_lbs read_values (drop i γ.(msc_shard_names)) }}}.
  Proof.
    intros Hlower Hγlen Hi.
    remember (T - i) as fuel eqn:Hfuel.
    revert i acc Hi Hfuel.
    induction fuel as [|fuel IH]; intros i acc Hi Hfuel.
    - have -> : i = T by lia.
      iIntros (Φ) "[#Hinv #Hlowerlbs] HΦ".
      rewrite /msc_sum_loop. wp_rec. wp_pures.
      rewrite bool_decide_eq_true_2; last done. wp_if.
      iApply ("HΦ" $! acc).
      have Hdrop_lower : drop T lower = [] by apply drop_ge; lia.
      have Hdrop_names : drop T γ.(msc_shard_names) = [] by
        apply drop_ge; lia.
      iExists []. rewrite Hdrop_lower Hdrop_names /msc_lbs /=.
      auto.
    - have Hit : i < T by lia.
      have HiS : S i ≤ T by lia.
      have HfuelS : fuel = T - S i by lia.
      have Hi1 : i + 1 ≤ T by lia.
      have Hfuel1 : fuel = T - (i + 1) by lia.
      destruct (lookup_lt_is_Some_2 lower i) as [n0 Hn0];
        first by rewrite Hlower.
      destruct (lookup_lt_is_Some_2 γ.(msc_shard_names) i) as [γi Hγi];
        first by rewrite Hγlen.
      iIntros (Φ) "[#Hinv #Hlowerlbs] HΦ".
      iPoseProof (big_sepL2_lookup _ _ _ i n0 γi Hn0 Hγi
        with "Hlowerlbs") as "#Hn0".
      rewrite /msc_sum_loop. wp_rec. wp_pures.
      rewrite bool_decide_eq_false_2; last naive_solver lia. wp_if.
      wp_pures.
      wp_bind (! _)%E.
      wp_apply (msc_load_shard γ a i γi n0 with "[$Hinv $Hn0]");
        first done.
      iIntros (n) "[#Hn %Hn0n]".
      wp_let.
      fold msc_sum_loop.
      wp_bind (msc_sum_loop #a #T
        (#(i : nat) + #1) (#(acc : nat) + #(n : nat)))%E.
      wp_binop. rewrite -Nat2Z.inj_add.
      wp_binop.
      replace (Z.of_nat i + 1)%Z with (Z.of_nat (i + 1)) by lia.
      wp_apply (IH (i + 1) (acc + n) Hi1 Hfuel1
        with "[$Hinv $Hlowerlbs]").
      iIntros (r) "Hpost".
      iDestruct "Hpost" as (read_values)
        "(%Hreadlen & %Hr & %Hlowerread & #Hreadlbs)".
      rewrite Nat.add_1_r in Hreadlen, Hlowerread.
      iEval (rewrite Nat.add_1_r) in "Hreadlbs".
      iApply ("HΦ" $! r).
      iExists (n :: read_values).
      iSplit.
      { iPureIntro. simpl. rewrite Hreadlen. lia. }
      iSplit.
      { iPureIntro. simpl. lia. }
      rewrite (drop_S lower n0 i Hn0).
      iSplit.
      { iPureIntro. simpl. lia. }
      rewrite (drop_S γ.(msc_shard_names) γi i Hγi).
      rewrite /msc_lbs /=. iFrame "Hn Hreadlbs".
  Qed.

  Lemma msc_lbs_sum_le xs ys γs :
    length xs = length γs →
    length ys = length γs →
    msc_lbs xs γs -∗
    ([∗ list] _ ↦ n; γi ∈ ys; γs, mono_nat_auth_own γi 1 n) -∗
    ⌜sum_list xs ≤ sum_list ys⌝.
  Proof.
    revert ys γs.
    induction xs as [|x xs IH]; intros [|y ys] [|γi γs] Hxs Hys;
      simpl in Hxs, Hys; try lia.
    - rewrite /msc_lbs /=. iIntros "_ _". done.
    - rewrite /msc_lbs /=.
      iIntros "[#Hx Hxs] [Hy Hys]".
      iDestruct (mono_nat_lb_own_valid with "Hy Hx") as %[_ Hxy].
      have Hxs' : length xs = length γs by lia.
      have Hys' : length ys = length γs by lia.
      iDestruct (IH ys γs Hxs' Hys' with "Hxs Hys") as %Hsum.
      iPureIntro. simpl. lia.
  Qed.






  Lemma msc_new_counter_spec (T : nat) :
    {{{ ⌜0 < T⌝ }}}
      msc_new_counter #T @ mscE
    {{{ c γ, RET c;
        msc_is_counter γ c ∗
        ([∗ list] i ∈ seq 0 T,
          msc_handle γ #(i : nat)) ∗
        msc_frag γ 1%Qp 0 }}}.
  Proof.
    iIntros (Φ) "%HT HΦ".
    rewrite /msc_new_counter. wp_lam.
    wp_alloc a as "Ha"; first lia.
    iEval (rewrite Nat2Z.id) in "Ha".

    iMod (own_alloc (msc_auth_elem 0 ⋅ msc_frag_elem 1%Qp 0))
      as (γt) "[Hauth Hfrag]".
    { rewrite /msc_auth_elem /msc_frag_elem.
      apply frac_auth_valid. done. }

    iMod (ghost_map_alloc_empty (K:=nat) (V:=nat * gname))
      as (γreq) "Hrequests".
    iMod (msc_mono_alloc_zeros T) as (γs) "[%Hγslen Hγs]".
    set (γ := MscName γt T γs γreq).

    iAssert ([∗ list] i ↦ n ∈ replicate T (0 : nat),
        (a +ₗ i) ↦ #(n : nat))%I with "[Ha]" as "Hcells".
    { rewrite -(big_sepL_fmap (λ n : nat, #(n : nat))
          (λ i v, (a +ₗ i) ↦ v)%I (replicate T (0 : nat))).
      rewrite fmap_replicate /array. iFrame. }

    iAssert (msc_shards a (replicate T (0 : nat)) γs)
      with "[Hcells Hγs]" as "Hshards".
    { rewrite /msc_shards.
      iFrame "Hcells".
      rewrite big_sepL2_replicate_l; first iExact "Hγs".
      done. }

    iMod (inv_alloc mscN _ (msc_inv γ a)
      with "[Hauth Hshards Hrequests]") as "#Hinv".
    { iNext. iExists (replicate T (0 : nat)), (∅ : gmap nat (nat * gname)).
      iSplit; first by rewrite length_replicate.
      iSplit; first done.
      rewrite sum_list_replicate Nat.mul_0_r.
      rewrite /msc_requests big_sepM_empty. iFrame. }

    iPoseProof (msc_make_handles γ) as "Hhandles".
    wp_pures.
    iApply ("HΦ" $! (#a, #T)%V γ).
    iFrame "Hhandles Hfrag".
    iExists a. iFrame "Hinv". done.
  Qed.

  Lemma msc_incr_spec
      γ c h (P : iProp Σ) (Q : nat → iProp Σ) :
    (∀ total,
      □ (msc_auth γ total ∗ P
          ={mscE ∖ ↑mscN}=∗
         msc_auth γ (S total) ∗ Q total)) ⊢
    {{{ msc_is_counter γ c ∗ msc_handle γ h ∗ P }}}
      msc_incr c h @ mscE
    {{{ RET #();
        msc_is_counter γ c ∗ msc_handle γ h ∗
        ∃ total, Q total }}}.
  Proof.
    iIntros "#HVS".
    iIntros (Φ) "!# (#Hcounter & #Hhandle & HP) HΦ".
    iDestruct "Hcounter" as (a ->) "#Hinv".
    iDestruct "Hhandle" as (i) "[%Hh %Hi]".
    subst h.

    rewrite /msc_incr. wp_lam. wp_pures.
    wp_bind (FAA _ _)%E.
    iInv mscN as (ns requests)
      "(>%Hlen & >%Hγlen & >Hauth & >Hshards & Hrequests)" "Hclose".
    iDestruct "Hshards" as "[Hcells Hmonos]".

    have Hi_ns : i < length ns by lia.
    destruct (lookup_lt_is_Some_2 ns i Hi_ns) as [n Hn].
    have Hi_γs : i < length γ.(msc_shard_names) by lia.
    destruct (lookup_lt_is_Some_2 γ.(msc_shard_names) i Hi_γs)
      as [γi Hγi].
    iDestruct (big_sepL_insert_acc _ _ _ _ Hn with "Hcells")
      as "[Hl Hcells]".
    iDestruct (big_sepL2_insert_acc _ _ _ i n γi Hn Hγi with "Hmonos")
      as "[Hmono Hmonos]".

    wp_faa.
    iMod (mono_nat_own_update (S n) with "Hmono")
      as "[Hmono _]"; first lia.
    iMod ("HVS" $! (sum_list ns) with "[$Hauth $HP]")
      as "[Hauth HQ]".
    iMod (msc_requests_advance γ (sum_list ns) requests
      with "Hauth Hrequests") as "[Hauth Hrequests]".

    iEval (rewrite Z.add_1_r -Nat2Z.inj_succ) in "Hl".
    iDestruct ("Hcells" $! (S n) with "Hl") as "Hcells".
    iDestruct ("Hmonos" $! (S n) γi with "Hmono") as "Hmonos".
    iEval (rewrite (list_insert_id _ _ _ Hγi)) in "Hmonos".
    iMod ("Hclose" with "[Hauth Hcells Hmonos Hrequests]") as "_".
    { iNext. iExists (<[i := S n]> ns), requests.
      iSplit; first by rewrite length_insert.
      iSplit; first done.
      rewrite (msc_sum_list_insert_S _ _ _ Hn).
      rewrite /msc_shards. iFrame. }

    iModIntro. wp_pures.
    iApply "HΦ".
    iModIntro.
    iSplit.
    { iExists a. iFrame "Hinv". done. }
    iSplit.
    { iExists i. iPureIntro. split; done. }
    iExists (sum_list ns). iFrame.
  Qed.

  Lemma msc_read_spec
      γ c (P : iProp Σ) (Q : nat → iProp Σ) :
    (∀ total,
      □ (msc_auth γ total ∗ P
          ={mscE ∖ ↑mscN}=∗
         msc_auth γ total ∗ Q total)) ⊢
    {{{ msc_is_counter γ c ∗ P }}}
      msc_read c @ mscE
    {{{ (total : nat), RET #total;
        msc_is_counter γ c ∗ Q total }}}.
  Proof.
    iIntros "#HVS".
    iIntros (Φ) "!# (#Hcounter & HP) HΦ".
    iDestruct "Hcounter" as (a ->) "#Hinv".
    iMod (saved_pred_alloc Q DfracDiscarded) as (γQ) "#HQsaved";
      first done.

    rewrite /msc_read. wp_lam.
    wp_bind NewProph.
    iInv mscN as (initial requests)
      "(>%Hlen & >%Hγlen & >Hauth & >Hshards & Hrequests)" "Hclose".
    iDestruct "Hshards" as "[Hcells Hmonos]".
    iDestruct (msc_monos_snapshot with "Hmonos")
      as "[Hmonos #Hinitiallbs]".
    wp_apply wp_new_proph; first done.
    iIntros (pvs p) "Hp".
    set (predicted := msc_proph_total pvs).
    iPoseProof ("HVS" $! predicted) as "#HVSpredicted".

    iAssert (|={mscE ∖ ↑mscN}=> ∃ current_requests : gmap nat (nat * gname),
        msc_auth γ (sum_list initial) ∗
        msc_requests γ (sum_list initial) current_requests ∗
        ((⌜sum_list initial ≤ predicted⌝ ∗
          ∃ id : nat,
            id ↪[γ.(msc_request_name)] (predicted, γQ)) ∨
         (⌜predicted < sum_list initial⌝ ∗ P)))%I
      with "[HP Hauth Hrequests]" as "Hregistered".
    { destruct (decide (sum_list initial ≤ predicted)) as [Hle|Hlt].
      - iMod (msc_request_register γ (sum_list initial) predicted γQ
          requests P Q Hle with "HQsaved HVSpredicted Hauth Hrequests HP")
          as (id) "(Hauth & Hrequests & Hid)".
        iModIntro. iExists (<[id := (predicted, γQ)]> requests).
        iFrame "Hauth Hrequests". iLeft.
        iSplit; first done. iExists id. iExact "Hid".
      - iModIntro. iExists requests. iFrame "Hauth Hrequests".
        iRight. iFrame. iPureIntro. lia. }
    iMod "Hregistered" as (current_requests)
      "(Hauth & Hrequests & Hcase)".

    iMod ("Hclose" with "[Hauth Hcells Hmonos Hrequests]") as "_".
    { iNext. iExists initial, current_requests.
      iSplit; first done. iSplit; first done.
      iSplitL "Hauth"; first done.
      iSplitL "Hcells Hmonos".
      { rewrite /msc_shards. iFrame. }
      iExact "Hrequests". }
    iModIntro.

    wp_pures.
    wp_apply (msc_sum_loop_bounds γ a γ.(msc_size) 0 0 initial
      Hlen Hγlen with "[$Hinv $Hinitiallbs]"); first lia.
    iIntros (actual) "Hscan".
    iDestruct "Hscan" as (read_values)
      "(%Hreadlen & %Hactual & %Hlower & #Hreadlbs)".
    rewrite drop_0 in Hlower.
    iEval (rewrite drop_0) in "Hreadlbs".
    have Hinitial_actual : sum_list initial ≤ actual by lia.
    wp_let.

    iDestruct "Hcase" as
      "[(%Hinitial_predicted & Hid) | (%Hpredicted_initial & HP)]".
    - iDestruct "Hid" as (id) "Hid".
      wp_bind (ResolveProph #p #(actual : nat))%E.
      iInv "Hinv" as (final requests') "(>%Hfinallen & >%Hγlen' &
        >Hauth & >Hshards & Hrequests)" "Hclose".
      iDestruct "Hshards" as "[Hcells Hmonos]".
      have Hreadnames :
        length read_values = length γ.(msc_shard_names) by lia.
      have Hfinalnames :
        length final = length γ.(msc_shard_names) by lia.
      iDestruct (msc_lbs_sum_le read_values final γ.(msc_shard_names)
        Hreadnames Hfinalnames with "Hreadlbs Hmonos")
        as %Hactual_final.
      wp_apply (wp_resolve_proph with "[Hp]")
        as (pvs') "[%Hpvs Hp]"; first done.
      have Hpredicted_actual : predicted = actual.
      { subst pvs. apply msc_proph_total_cons. }
      subst predicted.
      iEval (rewrite Hpredicted_actual) in "Hid".
      have Hactual_final' : actual ≤ sum_list final by lia.
      iMod (msc_request_take γ (sum_list final) actual γQ id requests' Q
        Hactual_final' with "HQsaved Hid Hrequests")
        as "[Hrequests HQ]".

      iMod ("Hclose" with "[Hauth Hcells Hmonos Hrequests]") as "_".
      { iNext. iExists final, (delete id requests').
        iSplit; first done. iSplit; first done.
        iSplitL "Hauth"; first done.
        iSplitL "Hcells Hmonos".
        { rewrite /msc_shards. iFrame. }
        iExact "Hrequests". }
      iModIntro. wp_seq.
      iApply ("HΦ" $! actual).
      iModIntro.
      iSplit; first (iExists a; iFrame "Hinv"; done).
      iExact "HQ".

    - wp_bind (ResolveProph #p #(actual : nat))%E.
      wp_apply (wp_resolve_proph with "[Hp]")
        as (pvs') "[%Hpvs Hp]"; first done.
      have Hpredicted_actual : predicted = actual.
      { subst pvs. apply msc_proph_total_cons. }
      exfalso. lia.
  Qed.

  Definition modular_sharded_counter : modular_counter Σ := {|
    modular_new_counter := msc_new_counter;
    modular_incr := msc_incr;
    modular_read := msc_read;
    modular_counter_name := msc_name;
    modular_counter_namespace := mscN;
    modular_counter_mask := mscE;
    modular_counter_namespace_subset := mscN_subset_mscE;
    modular_is_counter := msc_is_counter;
    modular_handle := msc_handle;
    counter_auth := msc_auth;
    counter_frag := msc_frag;
    modular_is_counter_persistent := msc_is_counter_persistent;
    modular_handle_persistent := msc_handle_persistent;
    counter_frag_fractional := msc_frag_fractional;
    modular_new_counter_spec := msc_new_counter_spec;
    modular_incr_spec := msc_incr_spec;
    modular_read_spec := msc_read_spec;
  |}.





  Definition msc_incr_twice : val :=
    λ: "c" "h", msc_incr "c" "h";; msc_incr "c" "h".
  Definition msc_two_incr_twice_read : val :=
    λ: "c" "h1" "h2",
      (msc_incr_twice "c" "h1" ||| msc_incr_twice "c" "h2");;
      msc_read "c".

  Definition msc_clientN : namespace :=
    nroot .@ "sharded_counter_modular_client".

  Definition msc_client_inv
      (γ : msc_name) (γm γd : gname) (n : nat) : iProp Σ :=
    (∃ k1 k2 : nat,
       ghost_map_auth γm 1
         (<[1 := (k1, γd)]> (<[2 := (k2, γd)]>
            (∅ : gmap nat (nat * gname)))) ∗
       msc_frag γ 1%Qp (n + k1 + k2)) ∨
    ghost_map_auth γm 1 (∅ : gmap nat (nat * gname)).

  Lemma msc_auth_frag_agree γ (t m : nat) :
    msc_auth γ t -∗ msc_frag γ 1%Qp m -∗ ⌜t = m⌝.
  Proof.
    iIntros "Hauth Hfrag".
    iDestruct (own_valid_2 with "Hauth Hfrag") as %Hvalid.
    iPureIntro.
    rewrite /msc_auth_elem /msc_frag_elem in Hvalid.
    apply frac_auth_agree in Hvalid.
    apply (inj to_agree), leibniz_equiv in Hvalid.
    exact Hvalid.
  Qed.

  Lemma msc_client_incr_spec γ c h (γm γd : gname) (n i ki : nat) :
    i = 1 ∨ i = 2 →
    {{{ inv msc_clientN (msc_client_inv γ γm γd n) ∗
        msc_is_counter γ c ∗
        msc_handle γ h ∗
        i ↪[γm] (ki, γd) }}}
      msc_incr c h
    {{{ RET #(); i ↪[γm] (S ki, γd) }}}.
  Proof.
    iIntros (Hi Φ) "(#HclientInv & #Hcounter & #Hhandle & Helem) HΦ".
    iPoseProof (msc_incr_spec γ c h
        (i ↪[γm] (ki, γd))%I
        (λ _ : nat, i ↪[γm] (S ki, γd))%I
      with "[]") as "#Hincr".
    { iIntros (total) "!> [Hauth Helem]".
      rewrite /mscE.
      iInv msc_clientN as
        "[(%k1 & %k2 & >Hmap & >Hfrag) | >Hempty]" "Hclose"; last first.
      { iDestruct (ghost_map_lookup with "Hempty Helem") as %Hbad.
        rewrite lookup_empty in Hbad. discriminate Hbad. }
      iDestruct (ghost_map_lookup with "Hmap Helem") as %Hlookup.
      iDestruct (msc_auth_frag_agree with "Hauth Hfrag") as %->.
      iMod (msc_auth_frag_update γ _ _ (S (n + k1 + k2))
        with "Hauth Hfrag") as "[Hauth Hfrag]".
      iMod (ghost_map_update (S ki, γd) with "Hmap Helem")
        as "[Hmap Helem]".
      destruct Hi as [-> | ->].
      - rewrite lookup_insert_eq in Hlookup.
        assert (k1 = ki) as -> by congruence.
        iEval (rewrite insert_insert_eq) in "Hmap".
        iMod ("Hclose" with "[Hmap Hfrag]") as "_".
        { iNext. iLeft. iExists (S ki), k2.
          have -> : n + S ki + k2 = S (n + ki + k2) by lia.
          iFrame. }
        iModIntro. iFrame.
      - rewrite lookup_insert_ne in Hlookup; last lia.
        rewrite lookup_insert_eq in Hlookup.
        assert (k2 = ki) as -> by congruence.
        have Hmapeq :
          <[2 := (S ki, γd)]> (<[1 := (k1, γd)]> (<[2 := (ki, γd)]>
            (∅ : gmap nat (nat * gname))))
          = <[1 := (k1, γd)]> (<[2 := (S ki, γd)]> ∅).
        { rewrite insert_insert_ne; last lia.
          by rewrite insert_insert_eq. }
        iEval (rewrite Hmapeq) in "Hmap".
        iMod ("Hclose" with "[Hmap Hfrag]") as "_".
        { iNext. iLeft. iExists k1, (S ki).
          have -> : n + k1 + S ki = S (n + k1 + ki) by lia.
          iFrame. }
        iModIntro. iFrame. }
    wp_apply ("Hincr" with "[$Hcounter $Hhandle $Helem]").
    iIntros "(_ & _ & (%total & Helem))".
    iApply "HΦ". iFrame.
  Qed.

  Lemma msc_two_incr_twice_read_spec `{!spawnG Σ} γ c h1 h2 n :
    {{{ msc_is_counter γ c ∗
        msc_handle γ h1 ∗
        msc_handle γ h2 ∗
        msc_frag γ 1%Qp n }}}
      msc_two_incr_twice_read c h1 h2
    {{{ RET #(n + 4 : nat);
        msc_is_counter γ c ∗
        msc_handle γ h1 ∗
        msc_handle γ h2 ∗
        msc_frag γ 1%Qp (n + 4) }}}.
  Proof.
    iIntros (Φ) "(#Hcounter & #Hh1 & #Hh2 & Hfrag) HΦ".
    set (γd := γ.(msc_model_name)).

    iMod (ghost_map_alloc_empty (K:=nat) (V:=nat * gname)) as (γm) "Hmap".
    iMod (ghost_map_insert 2 (0, γd) with "Hmap") as "[Hmap Helem2]";
      first apply lookup_empty.
    iMod (ghost_map_insert 1 (0, γd) with "Hmap") as "[Hmap Helem1]";
      first (rewrite lookup_insert_ne; [apply lookup_empty | lia]).
    iMod (inv_alloc msc_clientN _ (msc_client_inv γ γm γd n)
      with "[Hmap Hfrag]") as "#HclientInv".
    { iNext. iLeft. iExists 0, 0.
      rewrite !Nat.add_0_r. iFrame. }

    rewrite /msc_two_incr_twice_read.
    wp_smart_apply (wp_par
        (λ _, 1 ↪[γm] ((2 : nat), γd))%I
        (λ _, 2 ↪[γm] ((2 : nat), γd))%I
      with "[Helem1] [Helem2]").
    - rewrite /msc_incr_twice.
      wp_smart_apply (msc_client_incr_spec γ c h1 γm γd n 1 0
          (or_introl eq_refl)
        with "[$HclientInv $Hcounter $Hh1 $Helem1]") as "Helem1".
      wp_smart_apply (msc_client_incr_spec γ c h1 γm γd n 1 1
          (or_introl eq_refl)
        with "[$HclientInv $Hcounter $Hh1 $Helem1]") as "Helem1".
      done.
    - rewrite /msc_incr_twice.
      wp_smart_apply (msc_client_incr_spec γ c h2 γm γd n 2 0
          (or_intror eq_refl)
        with "[$HclientInv $Hcounter $Hh2 $Helem2]") as "Helem2".
      wp_smart_apply (msc_client_incr_spec γ c h2 γm γd n 2 1
          (or_intror eq_refl)
        with "[$HclientInv $Hcounter $Hh2 $Helem2]") as "Helem2".
      done.
    - iIntros (v1 v2) "[Helem1 Helem2] !>".
      iPoseProof (msc_read_spec γ c
          (1 ↪[γm] ((2 : nat), γd) ∗ 2 ↪[γm] ((2 : nat), γd))%I
          (λ total : nat,
            ⌜total = (n + 4)%nat⌝ ∗ msc_frag γ 1%Qp (n + 4))%I
        with "[]") as "#Hread".
      { iIntros (total) "!> [Hauth [Helem1 Helem2]]".
        rewrite /mscE.
        iInv msc_clientN as
          "[(%k1 & %k2 & >Hmap & >Hfrag) | >Hempty]" "Hclose"; last first.
        { iDestruct (ghost_map_lookup with "Hempty Helem1") as %Hbad.
          rewrite lookup_empty in Hbad. discriminate Hbad. }
        iDestruct (ghost_map_lookup with "Hmap Helem1") as %Hl1.
        iDestruct (ghost_map_lookup with "Hmap Helem2") as %Hl2.
        rewrite lookup_insert_eq in Hl1.
        rewrite lookup_insert_ne in Hl2; last lia.
        rewrite lookup_insert_eq in Hl2.
        assert (k1 = 2) as -> by congruence.
        assert (k2 = 2) as -> by congruence.
        iDestruct (msc_auth_frag_agree with "Hauth Hfrag") as %Htotal.
        iMod (ghost_map_delete with "Hmap Helem1") as "Hmap".
        iMod (ghost_map_delete with "Hmap Helem2") as "Hmap".
        have Hdel :
          delete 2 (delete 1 (<[1 := ((2 : nat), γd)]>
            (<[2 := ((2 : nat), γd)]> (∅ : gmap nat (nat * gname)))))
          = ∅.
        { rewrite delete_insert_eq.
          rewrite delete_insert_ne; last lia.
          rewrite delete_empty delete_insert_eq.
          by rewrite delete_empty. }
        iEval (rewrite Hdel) in "Hmap".
        iMod ("Hclose" with "[Hmap]") as "_".
        { iNext. iRight. iFrame. }
        iModIntro.
        have Heq : n + 2 + 2 = n + 4 by lia.
        iEval (rewrite Heq) in "Hfrag".
        iFrame "Hauth Hfrag".
        iPureIntro. lia. }
      wp_smart_apply ("Hread" with "[$Hcounter $Helem1 $Helem2]").
      iIntros (total) "(_ & %Htotal & Hfrag)".
      subst total.
      iApply "HΦ".
      by iFrame "Hcounter Hh1 Hh2 Hfrag".
  Qed.



End proof.
