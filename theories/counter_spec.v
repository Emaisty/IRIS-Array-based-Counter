From iris.heap_lang Require Import proofmode notation.
From iris.prelude Require Import options.

Class counter (Σ : gFunctors) `{!heapGS Σ} := Counter {
  new_counter : val;
  incr : val;
  read : val;

  counter_name : Type;
  is_counter : counter_name → val → iProp Σ;
  handle : counter_name → val → nat → iProp Σ;

  is_counter_persistent γ c :: Persistent (is_counter γ c);

  new_counter_spec (T : nat) :
    {{{ ⌜0 < T⌝ }}}
      new_counter #T
    {{{ c γ, RET c;
        is_counter γ c ∗ [∗ list] i ∈ seq 0 T, handle γ #(i : nat) 0 }}};

  incr_spec γ c h n :
    {{{ is_counter γ c ∗ handle γ h n }}}
      incr c h
    {{{ RET #(); handle γ h (S n) }}};

  read_spec γ c h n :
    {{{ is_counter γ c ∗ handle γ h n }}}
      read c
    {{{ (m : nat), RET #m; handle γ h n ∗ ⌜n ≤ m⌝ }}};
}.

Section client.
  Context `{!heapGS Σ, !counter Σ}.

  Definition incr_twice : val := λ: "c" "h", incr "c" "h";; incr "c" "h".

  Lemma incr_twice_spec γ c h n :
    {{{ is_counter γ c ∗ handle γ h n }}}
      incr_twice c h
    {{{ RET #(); handle γ h (S (S n)) }}}.
  Proof.
    iIntros (Φ) "[#Hc Hh] HΦ".
    wp_lam. wp_pures.
    wp_apply (incr_spec with "[$Hc $Hh]"). iIntros "Hh".
    wp_pures.
    wp_apply (incr_spec with "[$Hc $Hh]"). iIntros "Hh".
    by iApply "HΦ".
  Qed.
End client.
