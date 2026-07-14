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

  modular_is_counter : modular_counter_name → val → iProp Σ;
  modular_handle : modular_counter_name → val → iProp Σ;
  counter_model : modular_counter_name → Qp → nat → iProp Σ;

  modular_is_counter_persistent γ c ::
    Persistent (modular_is_counter γ c);

  modular_handle_persistent γ h ::
    Persistent (modular_handle γ h);

  counter_model_fractional γ n ::
    Fractional (λ q, counter_model γ q n);

  modular_new_counter_spec (E : coPset) (T : nat) :
    ↑modular_counter_namespace ⊆ E →
    {{{ ⌜0 < T⌝ }}}
      modular_new_counter #T @ E
    {{{ c γ, RET c;
        modular_is_counter γ c ∗
        ([∗ list] i ∈ seq 0 T,
          modular_handle γ #(i : nat)) ∗
        counter_model γ (1 / 2)%Qp 0 }}};

  modular_incr_spec
      (E : coPset) γ c h
      (P : iProp Σ) (Q : nat → iProp Σ) :
    ↑modular_counter_namespace ⊆ E →
    (∀ total,
      □ (counter_model γ (1 / 2)%Qp total ∗ P
          ={E ∖ ↑modular_counter_namespace}=∗
         counter_model γ (1 / 2)%Qp (S total) ∗ Q total)) ⊢
    {{{ modular_is_counter γ c ∗
        modular_handle γ h ∗ P }}}
      modular_incr c h @ E
    {{{ RET #();
        modular_is_counter γ c ∗
        modular_handle γ h ∗
        ∃ total, Q total }}};


  modular_read_spec
      (E : coPset) γ c
      (P : iProp Σ) (Q : nat → iProp Σ) :
    ↑modular_counter_namespace ⊆ E →
    (∀ total,
      □ (counter_model γ (1 / 2)%Qp total ∗ P
          ={E ∖ ↑modular_counter_namespace}=∗
         counter_model γ (1 / 2)%Qp total ∗ Q total)) ⊢
    {{{ modular_is_counter γ c ∗ P }}}
      modular_read c @ E
    {{{ (total : nat), RET #total;
        modular_is_counter γ c ∗
        Q total }}};
}.
