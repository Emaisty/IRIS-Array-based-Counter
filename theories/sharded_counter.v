From iris.algebra Require Import auth numbers.
From iris.algebra.lib Require Import excl_auth.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import par.
From iris.prelude Require Import options.

From summer_project Require Import counter_spec.


Definition sc_new_counter : val :=
  λ: "T", (AllocN "T" #0, "T").

Definition sc_incr : val :=
  λ: "c" "k",
    let: "l" := (Fst "c") +ₗ "k" in
    "l" <- ! "l" + #1.

Definition sc_read : val :=
  λ: "c",
    let: "a" := Fst "c" in
    let: "T" := Snd "c" in
    (rec: "sum" "i" :=
       if: "i" = "T" then #0
       else ! ("a" +ₗ "i") + "sum" ("i" + #1)) #0.


Definition sc_sum_loop (a : loc) (T : nat) : val :=
  rec: "sum" "i" :=
    if: "i" = #T then #0
    else ! (#a +ₗ "i") + "sum" ("i" + #1).


Class dcounterG Σ := DCounterG {
  dcounter_totalG :: inG Σ (authR natUR);
  dcounter_cellG :: inG Σ (excl_authR natO);
}.

Definition dcounterΣ : gFunctors :=
  #[GFunctor (authR natUR); GFunctor (excl_authR natO)].

Global Instance subG_dcounterΣ Σ : subG dcounterΣ Σ → dcounterG Σ.
Proof. solve_inG. Qed.

Definition dcounterN : namespace := nroot .@ "dcounter".


Section proof.
  Context `{!heapGS Σ, !dcounterG Σ}.
  Definition sc_name : Type := gname * list gname.

  Definition counter_inv (γ : sc_name) (a : loc) : iProp Σ :=
    ∃ ns : list nat,
      own γ.1 (● sum_list ns) ∗
      [∗ list] i ↦ γl; n ∈ γ.2; ns,
        (a +ₗ i) ↦ #(n : nat) ∗ own γl (●E n).

  Definition sc_is_counter (γ : sc_name) (v : val) : iProp Σ :=
    ∃ a : loc,
      ⌜v = (#a, #(length γ.2))%V⌝ ∗ inv dcounterN (counter_inv γ a).

  Global Instance sc_is_counter_persistent γ v :
    Persistent (sc_is_counter γ v).
  Proof. apply _. Qed.

  Definition sc_handle (γ : sc_name) (h : val) (n : nat) : iProp Σ :=
    ∃ (i : nat) (γl : gname),
      ⌜h = #i⌝ ∗ ⌜γ.2 !! i = Some γl⌝ ∗
      own γl (◯E n) ∗ own γ.1 (◯ n).


  (** ** Specifications *)


  Lemma alloc_cell_ghosts (T : nat) :
    ⊢ |==> ∃ γs : list gname,
      ⌜length γs = T⌝ ∗
      [∗ list] γl ∈ γs,
        own γl (●E (0 : nat)) ∗ own γl (◯E (0 : nat)).
  Proof.
    induction T as [|T IH].
    - iModIntro. iExists []. by rewrite /=.
    - iMod (own_alloc (●E (0 : nat) ⋅ ◯E (0 : nat)))
        as (γl) "[Hγl Hγlf]"; first apply excl_auth_valid.
      iMod IH as (γs Hγs) "Hγs".
      iModIntro. iExists (γl :: γs). rewrite /= Hγs. iFrame. done.
  Qed.

  Lemma big_sepL_index_seq {A} (l : list A) (P : nat → iProp Σ) :
    ([∗ list] i ↦ _ ∈ l, P i) ⊣⊢ [∗ list] i ∈ seq 0 (length l), P i.
  Proof.
    induction l as [|x l IH] in P |- *; simpl; first done.
    rewrite IH -fmap_S_seq big_sepL_fmap. done.
  Qed.

  Lemma make_initial_handles γt γs :
    own γt (◯ (0 : nat)) -∗
    ([∗ list] γl ∈ γs, own γl (◯E (0 : nat))) -∗
    [∗ list] i ∈ seq 0 (length γs), sc_handle (γt, γs) #(i : nat) 0.
  Proof.
    iIntros "Hzero Hfrags". iDestruct "Hzero" as "#Hzero".
    iAssert ([∗ list] _ ∈ γs, own γt (◯ (0 : nat)))%I
      with "[#]" as "#Hzeros".
    { iApply big_sepL_intro. iIntros "!>" (i γl Hγl). iFrame "Hzero". }
    iDestruct (big_sepL_sep_2 with "Hfrags Hzeros") as "Hresources".
    rewrite -big_sepL_index_seq.
    iApply (big_sepL_mono with "Hresources").
    iIntros (i γl Hγl) "[Hfrag Hzero']".
    iExists i, γl. simpl. iSplit; first done.
    iSplit; first (iPureIntro; exact Hγl).
    iFrame.
  Qed.

  Lemma alloc_initial_inv a γt γs :
    own γt (● (0 : nat)) -∗
    ([∗ list] γl ∈ γs, own γl (●E (0 : nat))) -∗
    a ↦∗ replicate (length γs) #0 ={⊤}=∗
    inv dcounterN (counter_inv (γt, γs) a).
  Proof.
    iIntros "Htotal Hauths Ha".
    iAssert ([∗ list] i ↦ n ∈ replicate (length γs) (0 : nat),
        (a +ₗ i) ↦ #(n : nat))%I with "[Ha]" as "Hcells".
    { rewrite -(big_sepL_fmap (λ n : nat, #(n : nat))
          (λ i v, (a +ₗ i) ↦ v)%I (replicate (length γs) (0 : nat))).
      rewrite fmap_replicate /array. iFrame. }
    iAssert ([∗ list] i ↦ γl; n ∈ γs; replicate (length γs) (0 : nat),
        (a +ₗ i) ↦ #(n : nat) ∗ own γl (●E n))%I
      with "[Hauths Hcells]" as "Hinv_cells".
    { iDestruct (big_sepL2_sepL_2
          (λ _ γl, own γl (●E (0 : nat)))
          (λ i n, ((a +ₗ i) ↦ #(n : nat))%I)
          γs (replicate (length γs) (0 : nat)) with "Hauths Hcells")
        as "Hboth"; first by rewrite length_replicate.
      iApply (big_sepL2_mono with "Hboth").
      iIntros (i γl n _ Hn) "[Hauth Hcell]".
      apply lookup_replicate in Hn as [-> _]. iFrame. }
    iMod (inv_alloc dcounterN _ (counter_inv (γt, γs) a)
      with "[Htotal Hinv_cells]") as "#Hinv".
    { iNext. iExists (replicate (length γs) (0 : nat)).
      rewrite sum_list_replicate Nat.mul_0_r. iFrame. }
    iModIntro. iExact "Hinv".
  Qed.

  Lemma sum_list_insert_S ns i n :
    ns !! i = Some n → sum_list (<[i := S n]> ns) = S (sum_list ns).
  Proof.
    revert i. induction ns as [|m ns IH]; intros [|i] Hlookup;
      simpl in Hlookup |- *; simplify_eq; first lia.
    rewrite (IH i Hlookup). lia.
  Qed.

  Lemma lookup_aligned {A B} (xs : list A) (ys : list B) i x :
    xs !! i = Some x → length xs = length ys → is_Some (ys !! i).
  Proof.
    intros Hx Hlen. apply lookup_lt_is_Some_2. rewrite -Hlen.
    exact (lookup_lt_Some _ _ _ Hx).
  Qed.

  Lemma cell_ghost_agree γl m n :
    own γl (●E m) -∗ own γl (◯E n) -∗ ⌜m = n⌝.
  Proof.
    iIntros "Hauth Hfrag".
    iDestruct (own_valid_2 with "Hauth Hfrag") as %Hvalid.
    iPureIntro. exact (excl_auth_agree_L _ _ Hvalid).
  Qed.

  Lemma cell_ghost_incr γl n :
    own γl (●E n) -∗ own γl (◯E n) ==∗
    own γl (●E (S n)) ∗ own γl (◯E (S n)).
  Proof.
    iIntros "Hauth Hfrag".
    iMod (own_update_2 with "Hauth Hfrag") as "[$ $]";
      first apply excl_auth_update. done.
  Qed.

  Lemma total_ghost_incr γt m n :
    own γt (● m) -∗ own γt (◯ n) ==∗
    own γt (● (S m)) ∗ own γt (◯ (S n)).
  Proof.
    iIntros "Hauth Hfrag".
    iMod (own_update_2 with "Hauth Hfrag") as "[$ $]";
      first (apply auth_update, (nat_local_update _ _ (S m) (S n)); lia).
    done.
  Qed.

  Lemma sc_new_counter_spec (T : nat) :
    {{{ ⌜0 < T⌝ }}}
      sc_new_counter #T
    {{{ c γ, RET c;
        sc_is_counter γ c ∗
        [∗ list] i ∈ seq 0 T, sc_handle γ #(i : nat) 0 }}}.
  Proof.
    iIntros (Φ) "%HT HΦ".
    rewrite /sc_new_counter. wp_lam.
    wp_alloc a as "Ha"; first lia.
    iEval (rewrite Nat2Z.id) in "Ha".

    iMod (alloc_cell_ghosts T) as (γs Hγs) "Hghosts".
    iDestruct (big_sepL_sep with "Hghosts") as "[Hauths Hfrags]".

    iMod (own_alloc (● (0 : nat) ⋅ ◯ (0 : nat)))
      as (γt) "[Htotal Hzero]"; first by apply auth_both_valid_2.

    iEval (rewrite -Hγs) in "Ha".
    iMod (alloc_initial_inv with "Htotal Hauths Ha") as "#Hinv".

    iDestruct (make_initial_handles with "Hzero Hfrags") as "Hhandles".
    iEval (rewrite Hγs) in "Hhandles".

    wp_pures.
    iApply ("HΦ" $! (#a, #T)%V (γt, γs)).
    iFrame "Hhandles". iExists a. simpl. iFrame "Hinv".
    iPureIntro. by rewrite Hγs.
  Qed.

  Lemma sc_load_cell γ a (i : nat) γl (n : nat) :
    γ.2 !! i = Some γl →
    {{{ inv dcounterN (counter_inv γ a) ∗ own γl (◯E n) }}}
      ! #(a +ₗ i)
    {{{ RET #(n : nat); own γl (◯E n) }}}.
  Proof.
    iIntros (Hγl Φ) "[#Hinv Hγlf] HΦ".
    iInv dcounterN as (ns) ">[Htotal Hcells]" "Hclose".
    iDestruct (big_sepL2_length with "Hcells") as %Hlen.
    destruct (lookup_aligned _ _ _ _ Hγl Hlen) as [m Hm].
    iDestruct (big_sepL2_lookup_acc _ _ _ _ _ _ Hγl Hm with "Hcells")
      as "[[Hl Hγla] Hcells]".
    iDestruct (cell_ghost_agree with "Hγla Hγlf") as %->.
    wp_load.
    iDestruct ("Hcells" with "[$Hl $Hγla]") as "Hcells".
    iMod ("Hclose" with "[Htotal Hcells]") as "_".
    { iNext. iExists ns. iFrame. }
    iModIntro. by iApply "HΦ".
  Qed.

  Lemma sc_store_cell γ a (i : nat) γl (n : nat) :
    γ.2 !! i = Some γl →
    {{{ inv dcounterN (counter_inv γ a) ∗
        own γl (◯E n) ∗ own γ.1 (◯ n) }}}
      #(a +ₗ i) <- #(n : nat) + #1
    {{{ RET #(); own γl (◯E (S n)) ∗ own γ.1 (◯ (S n)) }}}.
  Proof.
    iIntros (Hγl Φ) "(#Hinv & Hγlf & Htotalf) HΦ". wp_pures.
    iInv dcounterN as (ns) ">[Htotal Hcells]" "Hclose".
    iDestruct (big_sepL2_length with "Hcells") as %Hlen.
    destruct (lookup_aligned _ _ _ _ Hγl Hlen) as [m Hm].
    iDestruct (big_sepL2_insert_acc _ _ _ _ _ _ Hγl Hm with "Hcells")
      as "[[Hl Hγla] Hcells]".
    iDestruct (cell_ghost_agree with "Hγla Hγlf") as %->.
    iMod (cell_ghost_incr with "Hγla Hγlf") as "[Hγla Hγlf]".
    iMod (total_ghost_incr with "Htotal Htotalf") as "[Htotal Htotalf]".
    wp_store. iEval (rewrite Z.add_1_r -Nat2Z.inj_succ) in "Hl".
    iDestruct ("Hcells" $! γl (S n) with "[$Hl $Hγla]") as "Hcells".
    iEval (rewrite (list_insert_id _ _ _ Hγl)) in "Hcells".
    iMod ("Hclose" with "[Htotal Hcells]") as "_".
    { iNext. iExists (<[i := S n]> ns).
      rewrite (sum_list_insert_S _ _ _ Hm). iFrame. }
    iModIntro. iApply "HΦ". iFrame.
  Qed.

  Lemma sc_load_any_cell γ a (i : nat) :
    i < length γ.2 →
    {{{ inv dcounterN (counter_inv γ a) }}}
      ! #(a +ₗ i)
    {{{ (n : nat), RET #(n : nat); True }}}.
  Proof.
    iIntros (Hi Φ) "#Hinv HΦ".
    destruct (lookup_lt_is_Some_2 γ.2 i Hi) as [γl Hγl].
    iInv dcounterN as (ns) ">[Htotal Hcells]" "Hclose".
    iDestruct (big_sepL2_length with "Hcells") as %Hlen.
    destruct (lookup_aligned _ _ _ _ Hγl Hlen) as [n Hn].
    iDestruct (big_sepL2_lookup_acc _ _ _ _ _ _ Hγl Hn with "Hcells")
      as "[[Hl Hγla] Hcells]".
    wp_load.
    iDestruct ("Hcells" with "[$Hl $Hγla]") as "Hcells".
    iMod ("Hclose" with "[Htotal Hcells]") as "_".
    { iNext. iExists ns. iFrame. }
    iModIntro. iApply ("HΦ" $! n). done.
  Qed.

  Lemma sc_sum_loop_spec γ a T j :
    length γ.2 = T → j ≤ T →
    {{{ inv dcounterN (counter_inv γ a) }}}
      sc_sum_loop a T #(j : nat)
    {{{ (n : nat), RET #(n : nat); True }}}.
  Proof.
    intros Hlen Hj.
    remember (T - j) as fuel eqn:Hfuel.
    revert j Hj Hfuel.
    induction fuel as [|fuel IH]; intros j Hj Hfuel.
    - have -> : j = T by lia.
      iIntros (Φ) "#Hinv HΦ". rewrite /sc_sum_loop. wp_rec. wp_pures.
      rewrite bool_decide_eq_true_2; last done. wp_if.
      iApply ("HΦ" $! 0%nat with "[//]").
    - have Hlt : j < T by lia.
      iIntros (Φ) "#Hinv HΦ". rewrite /sc_sum_loop. wp_rec. wp_pures.
      rewrite bool_decide_eq_false_2; last naive_solver lia. wp_if.
      have Hj' : S j ≤ T by lia.
      have Hfuel' : fuel = T - S j by lia.
      wp_bind (sc_sum_loop a T (#(j : nat) + #1))%E.
      wp_binop. rewrite Z.add_1_r -Nat2Z.inj_succ.
      wp_apply (IH (S j) Hj' Hfuel' with "Hinv").
      iIntros (m) "_".
      wp_bind (! _)%E. wp_pures.
      wp_apply (sc_load_any_cell with "Hinv"); first by rewrite Hlen.
      iIntros (n) "_". wp_pures. rewrite -Nat2Z.inj_add.
      iApply ("HΦ" $! (n + m)%nat). done.
  Qed.

  Lemma sc_sum_loop_handle_spec γ a T i γl n j :
    length γ.2 = T → γ.2 !! i = Some γl → j ≤ i → i < T →
    {{{ inv dcounterN (counter_inv γ a) ∗ own γl (◯E n) }}}
      sc_sum_loop a T #(j : nat)
    {{{ (m : nat), RET #(m : nat); own γl (◯E n) ∗ ⌜n ≤ m⌝ }}}.
  Proof.
    intros Hlen Hγl Hj Hi.
    remember (i - j) as fuel eqn:Hfuel.
    revert j Hj Hfuel.
    induction fuel as [|fuel IH]; intros j Hj Hfuel.
    - have -> : j = i by lia.
      iIntros (Φ) "[#Hinv Hγlf] HΦ". rewrite /sc_sum_loop. wp_rec. wp_pures.
      rewrite bool_decide_eq_false_2; last naive_solver lia. wp_if.
      wp_bind (sc_sum_loop a T (#(i : nat) + #1))%E.
      wp_binop. rewrite Z.add_1_r -Nat2Z.inj_succ.
      wp_apply (sc_sum_loop_spec γ a T (S i) with "Hinv"); [done|lia|].
      iIntros (m) "_".
      wp_bind (! _)%E. wp_pures.
      wp_apply (sc_load_cell with "[$Hinv $Hγlf]"); first exact Hγl.
      iIntros "Hγlf". wp_pures. rewrite -Nat2Z.inj_add.
      iApply ("HΦ" $! (n + m)%nat). iFrame. iPureIntro. lia.
    - have Hji : j < i by lia.
      iIntros (Φ) "[#Hinv Hγlf] HΦ". rewrite /sc_sum_loop. wp_rec. wp_pures.
      rewrite bool_decide_eq_false_2; last naive_solver lia. wp_if.
      have Hj' : S j ≤ i by lia.
      have Hfuel' : fuel = i - S j by lia.
      wp_bind (sc_sum_loop a T (#(j : nat) + #1))%E.
      wp_binop. rewrite Z.add_1_r -Nat2Z.inj_succ.
      wp_apply (IH (S j) Hj' Hfuel' with "[$Hinv $Hγlf]").
      iIntros (m) "[Hγlf %Hnm]".
      wp_bind (! _)%E. wp_pures.
      wp_apply (sc_load_any_cell with "Hinv"); first by rewrite Hlen; lia.
      iIntros (k) "_". wp_pures. rewrite -Nat2Z.inj_add.
      iApply ("HΦ" $! (k + m)%nat). iFrame. iPureIntro. lia.
  Qed.

  Lemma sc_sum_loop_two_handles_spec
      γ a T i γi n j γj m start :
    length γ.2 = T →
    γ.2 !! i = Some γi →
    γ.2 !! j = Some γj →
    start ≤ i → i < j → j < T →
    {{{ inv dcounterN (counter_inv γ a) ∗
        own γi (◯E n) ∗ own γj (◯E m) }}}
      sc_sum_loop a T #(start : nat)
    {{{ (r : nat), RET #(r : nat);
        own γi (◯E n) ∗ own γj (◯E m) ∗ ⌜n + m ≤ r⌝ }}}.
  Proof.
    intros Hlen Hγi Hγj Hstart Hij HjT.
    remember (i - start) as fuel eqn:Hfuel.
    revert start Hstart Hfuel.
    induction fuel as [|fuel IH]; intros start Hstart Hfuel.
    - have -> : start = i by lia.
      iIntros (Φ) "(#Hinv & Hγif & Hγjf) HΦ".
      rewrite /sc_sum_loop. wp_rec. wp_pures.
      rewrite bool_decide_eq_false_2; last naive_solver lia. wp_if.

      wp_bind (sc_sum_loop a T (#(i : nat) + #1))%E.
      wp_binop. rewrite Z.add_1_r -Nat2Z.inj_succ.
      wp_apply (sc_sum_loop_handle_spec γ a T j γj m (S i)
        with "[$Hinv $Hγjf]"); [done|exact Hγj|lia|exact HjT|].
      iIntros (r) "[Hγjf %Hmr]".

      wp_bind (! _)%E. wp_pures.
      wp_apply (sc_load_cell with "[$Hinv $Hγif]"); first exact Hγi.
      iIntros "Hγif".
      wp_pures. rewrite -Nat2Z.inj_add.

      iApply ("HΦ" $! (n + r)%nat). iFrame. iPureIntro. lia.
    - have Hstarti : start < i by lia.
      iIntros (Φ) "(#Hinv & Hγif & Hγjf) HΦ".
      rewrite /sc_sum_loop. wp_rec. wp_pures.
      rewrite bool_decide_eq_false_2; last naive_solver lia. wp_if.

      have Hstart' : S start ≤ i by lia.
      have Hfuel' : fuel = i - S start by lia.
      wp_bind (sc_sum_loop a T (#(start : nat) + #1))%E.
      wp_binop. rewrite Z.add_1_r -Nat2Z.inj_succ.
      wp_apply (IH (S start) Hstart' Hfuel'
        with "[$Hinv $Hγif $Hγjf]").
      iIntros (r) "(Hγif & Hγjf & %Hnmr)".

      wp_bind (! _)%E. wp_pures.
      wp_apply (sc_load_any_cell with "Hinv");
        first by rewrite Hlen; lia.
      iIntros (k) "_".
      wp_pures. rewrite -Nat2Z.inj_add.

      iApply ("HΦ" $! (k + r)%nat). iFrame. iPureIntro. lia.
  Qed.


  Lemma sc_incr_spec γ c h n :
    {{{ sc_is_counter γ c ∗ sc_handle γ h n }}}
      sc_incr c h
    {{{ RET #(); sc_handle γ h (S n) }}}.
  Proof.
    iIntros (Φ) "[Hcounter Hhandle] HΦ".
    iDestruct "Hcounter" as (a ->) "#Hinv".
    iDestruct "Hhandle" as (i γl -> Hγl) "[Hγlf Htotalf]".

    rewrite /sc_incr. wp_lam. wp_pures.

    wp_apply (sc_load_cell with "[$Hinv $Hγlf]"); first exact Hγl.
    iIntros "Hγlf".

    wp_apply (sc_store_cell with "[$Hinv $Hγlf $Htotalf]"); first exact Hγl.
    iIntros "[Hγlf Htotalf]".

    iApply "HΦ".
    iExists i, γl. iFrame. iSplit; done.
  Qed.

  Lemma sc_read_spec γ c h n :
    {{{ sc_is_counter γ c ∗ sc_handle γ h n }}}
      sc_read c
    {{{ (m : nat), RET #m; sc_handle γ h n ∗ ⌜n ≤ m⌝ }}}.
  Proof.
    iIntros (Φ) "[Hcounter Hhandle] HΦ".
    iDestruct "Hcounter" as (a ->) "#Hinv".
    iDestruct "Hhandle" as (i γl -> Hγl) "[Hγlf Htotalf]".

    have Hi : i < length γ.2 := lookup_lt_Some _ _ _ Hγl.

    rewrite /sc_read. wp_lam. wp_proj. wp_let. wp_proj. wp_let.
    fold (sc_sum_loop a (length γ.2)).

    wp_smart_apply (sc_sum_loop_handle_spec γ a (length γ.2) i γl n 0
      with "[$Hinv $Hγlf]"); [done|exact Hγl|lia|exact Hi|].
    iIntros (m) "[Hγlf %Hnm]".

    iApply "HΦ". iSplit; last done.
    iExists i, γl. iFrame. iSplit; done.
  Qed.

  Lemma sc_read_two_handles_spec γ c h1 h2 n m :
    {{{ sc_is_counter γ c ∗
        sc_handle γ h1 n ∗ sc_handle γ h2 m }}}
      sc_read c
    {{{ (k : nat), RET #k;
        sc_handle γ h1 n ∗ sc_handle γ h2 m ∗ ⌜n + m ≤ k⌝ }}}.
  Proof.
    iIntros (Φ) "(Hcounter & Hhandle1 & Hhandle2) HΦ".
    iDestruct "Hcounter" as (a ->) "#Hinv".
    iDestruct "Hhandle1" as (i γi -> Hγi) "[Hγif Htotal1]".
    iDestruct "Hhandle2" as (j γj -> Hγj) "[Hγjf Htotal2]".

    have HiT : i < length γ.2 := lookup_lt_Some _ _ _ Hγi.
    have HjT : j < length γ.2 := lookup_lt_Some _ _ _ Hγj.

    rewrite /sc_read. wp_lam. wp_proj. wp_let. wp_proj. wp_let.
    fold (sc_sum_loop a (length γ.2)).

    destruct (Nat.lt_trichotomy i j) as [Hij|[Hij|Hij]].
    - wp_smart_apply (sc_sum_loop_two_handles_spec
        γ a (length γ.2) i γi n j γj m 0
        with "[$Hinv $Hγif $Hγjf]");
        [done|exact Hγi|exact Hγj|lia|exact Hij|exact HjT|].
      iIntros (k) "(Hγif & Hγjf & %Hnmk)".
      iApply "HΦ".
      iSplitL "Hγif Htotal1".
      { iExists i, γi. iFrame. iSplit; done. }
      iSplitL "Hγjf Htotal2".
      { iExists j, γj. iFrame. iSplit; done. }
      done.
    - subst j.
      have -> : γj = γi by naive_solver.
      iDestruct (own_valid_2 with "Hγif Hγjf")
        as %Hinvalid%excl_auth_frag_op_valid.
      done.
    - wp_smart_apply (sc_sum_loop_two_handles_spec
        γ a (length γ.2) j γj m i γi n 0
        with "[$Hinv $Hγjf $Hγif]");
        [done|exact Hγj|exact Hγi|lia|exact Hij|exact HiT|].
      iIntros (k) "(Hγjf & Hγif & %Hmnk)".
      iApply "HΦ".
      iSplitL "Hγif Htotal1".
      { iExists i, γi. iFrame. iSplit; done. }
      iSplitL "Hγjf Htotal2".
      { iExists j, γj. iFrame. iSplit; done. }
      iPureIntro. lia.
  Qed.


  Definition sharded_counter : counter Σ := {|
    new_counter := sc_new_counter;
    incr := sc_incr;
    read := sc_read;
    counter_name := sc_name;
    is_counter := sc_is_counter;
    handle := sc_handle;
    is_counter_persistent := sc_is_counter_persistent;
    new_counter_spec := sc_new_counter_spec;
    incr_spec := sc_incr_spec;
    read_spec := sc_read_spec;
  |}.

  Context `{!spawnG Σ}.


  Definition sc_incr_twice : val :=
    λ: "c" "h", sc_incr "c" "h";; sc_incr "c" "h".

  Definition sc_two_incr_twice_read : val :=
    λ: "c" "h1" "h2",
      (sc_incr_twice "c" "h1" ||| sc_incr_twice "c" "h2");;
      sc_read "c".

  Lemma sc_two_incr_twice_read_lower_bound_spec `{!spawnG Σ} γ c h1 h2 n m :
    {{{ sc_is_counter γ c ∗
        sc_handle γ h1 n ∗
        sc_handle γ h2 m }}}
      sc_two_incr_twice_read c h1 h2
    {{{ (k : nat), RET #k;
        sc_handle γ h1 (S (S n)) ∗
        sc_handle γ h2 (S (S m)) ∗
        ⌜n + m + 4 ≤ k⌝ }}}.
  Proof.
    iIntros (Φ) "(#Hcounter & Hhandle1 & Hhandle2) HΦ".
    rewrite /sc_two_incr_twice_read. wp_lam. wp_pures.

    wp_bind (par
      (λ: <>, sc_incr_twice c h1)%V
      (λ: <>, sc_incr_twice c h2)%V).
    iApply (par_spec
      (λ _, sc_handle γ h1 (S (S n)))%I
      (λ _, sc_handle γ h2 (S (S m)))%I
      (λ: <>, sc_incr_twice c h1)%V
      (λ: <>, sc_incr_twice c h2)%V
      with "[Hhandle1] [Hhandle2]").
    - wp_lam. rewrite /sc_incr_twice. wp_lam. wp_pures.

      wp_apply (sc_incr_spec with "[$Hcounter $Hhandle1]").
      iIntros "Hhandle1". wp_pures.

      wp_apply (sc_incr_spec with "[$Hcounter $Hhandle1]").
      iIntros "Hhandle1". iFrame.
    - wp_lam. rewrite /sc_incr_twice. wp_lam. wp_pures.

      wp_apply (sc_incr_spec with "[$Hcounter $Hhandle2]").
      iIntros "Hhandle2". wp_pures.

      wp_apply (sc_incr_spec with "[$Hcounter $Hhandle2]").
      iIntros "Hhandle2". iFrame.
    - iNext.
      iIntros (v1 v2) "[Hhandle1 Hhandle2]".
      iNext. wp_pures.

      wp_apply (sc_read_two_handles_spec
        with "[$Hcounter $Hhandle1 $Hhandle2]").
      iIntros (k) "(Hhandle1 & Hhandle2 & %Hlower)".

      iApply "HΦ". iFrame. iPureIntro. lia.
  Qed.
End proof.
