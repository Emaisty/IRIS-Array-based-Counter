From iris.algebra Require Import agree frac.
From iris.base_logic.lib Require Import invariants.
From iris.bi.lib Require Import fractional.
From iris.heap_lang Require Import proofmode notation.
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
    let: "a" := Fst "c" in
    let: "T" := Snd "c" in
    msc_sum_loop "a" "T" #0 #0.

Definition msc_modelR : cmra := prodR fracR (agreeR natO).

Class mscG Σ := MSCG {
  msc_modelG :: inG Σ msc_modelR;
}.

Definition mscΣ : gFunctors := #[GFunctor msc_modelR].

Global Instance subG_mscΣ Σ : subG mscΣ Σ → mscG Σ.
Proof. solve_inG. Qed.

Definition mscN : namespace := nroot .@ "sharded_counter_modular".

Definition msc_model_elem (q : Qp) (n : nat) : msc_modelR :=
  (q, to_agree n).
Typeclasses Opaque msc_model_elem.

Section model.
  Context `{!mscG Σ}.

  Global Instance msc_model_elem_fractional γ n :
    Fractional (λ q, own γ (msc_model_elem q n))%I.
  Proof.
    intros p q. rewrite /msc_model_elem -own_op.
    f_equiv. split; first done. by rewrite /= agree_idemp.
  Qed.

  Global Instance msc_model_elem_as_fractional γ q n :
    AsFractional (own γ (msc_model_elem q n))
      (λ q, own γ (msc_model_elem q n))%I q.
  Proof. split; first done. apply _. Qed.
End model.


Section proof.
  Context `{!heapGS Σ, !mscG Σ}.
  Definition msc_name : Type := gname * nat.

  Definition msc_model
      (γ : msc_name) (q : Qp) (n : nat) : iProp Σ :=
    own γ.1 (msc_model_elem q n).

  Global Instance msc_model_fractional γ n :
    Fractional (λ q, msc_model γ q n).
  Proof. apply _. Qed.


  Definition msc_inv (γ : msc_name) (a : loc) : iProp Σ :=
    ∃ ns : list nat,
      ⌜length ns = γ.2⌝ ∗
      msc_model γ (1 / 2)%Qp (sum_list ns) ∗
      [∗ list] i ↦ n ∈ ns, (a +ₗ i) ↦ #(n : nat).

  Definition msc_is_counter
      (γ : msc_name) (c : val) : iProp Σ :=
    ∃ a : loc,
      ⌜c = (#a, #(γ.2 : nat))%V⌝ ∗
      inv mscN (msc_inv γ a).

  Global Instance msc_is_counter_persistent γ c :
    Persistent (msc_is_counter γ c).
  Proof. apply _. Qed.

  Definition msc_handle (γ : msc_name) (h : val) : iProp Σ :=
    ∃ i : nat, ⌜h = #(i : nat)⌝ ∗ ⌜i < γ.2⌝.

  Global Instance msc_handle_persistent γ h :
    Persistent (msc_handle γ h).
  Proof. apply _. Qed.



  Lemma msc_make_handles γt T :
    ⊢ [∗ list] i ∈ seq 0 T, msc_handle (γt, T) #(i : nat).
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



  Lemma msc_new_counter_spec E (T : nat) :
    ↑mscN ⊆ E →
    {{{ ⌜0 < T⌝ }}}
      msc_new_counter #T @ E
    {{{ c γ, RET c;
        msc_is_counter γ c ∗
        ([∗ list] i ∈ seq 0 T,
          msc_handle γ #(i : nat)) ∗
        msc_model γ (1 / 2)%Qp 0 }}}.
  Proof.
    iIntros (Hsubset Φ) "%HT HΦ".
    rewrite /msc_new_counter. wp_lam.
    wp_alloc a as "Ha"; first lia.
    iEval (rewrite Nat2Z.id) in "Ha".

    iMod (own_alloc (msc_model_elem 1%Qp 0)) as (γt) "Hmodel";
      first done.
    iDestruct "Hmodel" as "[Hinternal Hclient]".

    iAssert ([∗ list] i ↦ n ∈ replicate T (0 : nat),
        (a +ₗ i) ↦ #(n : nat))%I with "[Ha]" as "Hcells".
    { rewrite -(big_sepL_fmap (λ n : nat, #(n : nat))
          (λ i v, (a +ₗ i) ↦ v)%I (replicate T (0 : nat))).
      rewrite fmap_replicate /array. iFrame. }

    iMod (inv_alloc mscN _ (msc_inv (γt, T) a)
      with "[Hinternal Hcells]") as "#Hinv".
    { iNext. iExists (replicate T (0 : nat)).
      iSplit; first by rewrite length_replicate.
      rewrite sum_list_replicate Nat.mul_0_r. iFrame. }

    iPoseProof (msc_make_handles γt T) as "Hhandles".
    wp_pures.
    iApply ("HΦ" $! (#a, #T)%V (γt, T)).
    iFrame "Hhandles Hclient".
    iExists a. iFrame "Hinv". done.
  Qed.



  Lemma msc_incr_spec
      E γ c h (P : iProp Σ) (Q : nat → iProp Σ) :
    ↑mscN ⊆ E →
    (∀ total,
      □ (msc_model γ (1 / 2)%Qp total ∗ P
          ={E ∖ ↑mscN}=∗
         msc_model γ (1 / 2)%Qp (S total) ∗ Q total)) ⊢
    {{{ msc_is_counter γ c ∗ msc_handle γ h ∗ P }}}
      msc_incr c h @ E
    {{{ RET #();
        msc_is_counter γ c ∗ msc_handle γ h ∗
        ∃ total, Q total }}}.
  Proof.
    iIntros (Hsubset) "#HVS".
    iIntros (Φ) "!# (#Hcounter & #Hhandle & HP) HΦ".
    iDestruct "Hcounter" as (a ->) "#Hinv".
    iDestruct "Hhandle" as (i) "[%Hh %Hi]".
    subst h.

    rewrite /msc_incr. wp_lam. wp_pures.
    wp_bind (FAA _ _)%E.
    iInv mscN as (ns) ">(%Hlen & Hmodel & Hcells)" "Hclose".

    have Hi_ns : i < length ns by lia.
    destruct (lookup_lt_is_Some_2 ns i Hi_ns) as [n Hn].
    iDestruct (big_sepL_insert_acc _ _ _ _ Hn with "Hcells")
      as "[Hl Hcells]".

    wp_faa.
    iMod ("HVS" $! (sum_list ns) with "[$Hmodel $HP]")
      as "[Hmodel HQ]".

    iEval (rewrite Z.add_1_r -Nat2Z.inj_succ) in "Hl".
    iDestruct ("Hcells" $! (S n) with "Hl") as "Hcells".
    iMod ("Hclose" with "[Hmodel Hcells]") as "_".
    { iNext. iExists (<[i := S n]> ns).
      iSplit; first by rewrite length_insert.
      rewrite (msc_sum_list_insert_S _ _ _ Hn). iFrame. }

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
      E γ c (P : iProp Σ) (Q : nat → iProp Σ) :
    ↑mscN ⊆ E →
    (∀ total,
      □ (msc_model γ (1 / 2)%Qp total ∗ P
          ={E ∖ ↑mscN}=∗
         msc_model γ (1 / 2)%Qp total ∗ Q total)) ⊢
    {{{ msc_is_counter γ c ∗ P }}}
      msc_read c @ E
    {{{ (total : nat), RET #total;
        msc_is_counter γ c ∗ Q total }}}.
  Proof.
  Admitted.


  Definition modular_sharded_counter : modular_counter Σ := {|
    modular_new_counter := msc_new_counter;
    modular_incr := msc_incr;
    modular_read := msc_read;
    modular_counter_name := msc_name;
    modular_counter_namespace := mscN;
    modular_is_counter := msc_is_counter;
    modular_handle := msc_handle;
    counter_model := msc_model;
    modular_is_counter_persistent := msc_is_counter_persistent;
    modular_handle_persistent := msc_handle_persistent;
    counter_model_fractional := msc_model_fractional;
    modular_new_counter_spec := msc_new_counter_spec;
    modular_incr_spec := msc_incr_spec;
    modular_read_spec := msc_read_spec;
  |}.

End proof.
