From iris.algebra Require Import frac.
From iris.base_logic.lib Require Import invariants.
From iris.bi.lib Require Import fractional.
From iris.heap_lang Require Import proofmode notation.
From iris.prelude Require Import options.

Class modular_counter (Σ : gFunctors) `{!heapGS Σ} := ModularCounter {
  modular_new_counter : val;

  modular_incr : val;

  modular_read : val;

  modular_counter_name : Type;

  modular_counter_namespace : namespace;

  modular_counter_mask : coPset;

  modular_counter_namespace_subset :
    ↑modular_counter_namespace ⊆ modular_counter_mask;

  modular_is_counter : modular_counter_name → val → iProp Σ;

  modular_handle : modular_counter_name → val → iProp Σ;

  counter_auth : modular_counter_name → nat → iProp Σ;

  counter_frag : modular_counter_name → Qp → nat → iProp Σ;

  modular_is_counter_persistent γ c ::
    Persistent (modular_is_counter γ c);

  modular_handle_persistent γ h ::
    Persistent (modular_handle γ h);

  counter_frag_fractional γ n ::
    Fractional (λ q, counter_frag γ q n);


  modular_new_counter_spec (T : nat) :
    {{{ ⌜0 < T⌝ }}}
      modular_new_counter #T @ modular_counter_mask
    {{{ c γ, RET c;
        modular_is_counter γ c ∗
        ([∗ list] i ∈ seq 0 T,
          modular_handle γ #(i : nat)) ∗
        counter_frag γ 1%Qp 0 }}};


  modular_incr_spec
      γ c h
      (P : iProp Σ) (Q : nat → iProp Σ) :
    (∀ total,
      □ (counter_auth γ total ∗ P
          ={modular_counter_mask ∖ ↑modular_counter_namespace}=∗
         counter_auth γ (S total) ∗ Q total)) ⊢
    {{{ modular_is_counter γ c ∗
        modular_handle γ h ∗ P }}}
      modular_incr c h @ modular_counter_mask
    {{{ RET #();
        modular_is_counter γ c ∗
        modular_handle γ h ∗
        ∃ total, Q total }}};


  modular_read_spec
      γ c
      (P : iProp Σ) (Q : nat → iProp Σ) :
    (∀ total,
      □ (counter_auth γ total ∗ P
          ={modular_counter_mask ∖ ↑modular_counter_namespace}=∗
         counter_auth γ total ∗ Q total)) ⊢
    {{{ modular_is_counter γ c ∗ P }}}
      modular_read c @ modular_counter_mask
    {{{ (total : nat), RET #total;
        modular_is_counter γ c ∗
        Q total }}};
}.
