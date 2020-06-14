lemma p_imp_not_n : ∀ (G : pimpartial), p_position G → ¬ (n_position G)
| (mk 0 M) :=
    begin
      intro hpG,
      rw zero_unique,
      exact zero_not_n_position
    end
| (mk (nat.succ n) M) :=
    begin
      intro hpG,
      intro hnG,
      unfold p_position at hpG,
      unfold n_position at hnG,

      cases hnG with i hnG',
      have hpG' := hpG i,
      cases hpG' with j hpG'',
      have hnG'' := hnG' j,

      -- For recursion
      have h1 : (((mk (nat.succ n) M).move i).move j).subsequent ((mk (nat.succ n) M).move i), from subsequent.from_move ((mk (nat.succ n) M).move i) j,
      have h2 : ((mk (nat.succ n) M).move i).subsequent (mk (nat.succ n) M), from subsequent.from_move (mk (nat.succ n) M) i,
      have hwf : (((mk (nat.succ n) M).move i).move j).subsequent (mk n.succ M), from subsequent.from_trans (((mk n.succ M).move i).move j) ((mk n.succ M).move i) (mk n.succ M) h1 h2,

      exact p_imp_not_n (((mk (nat.succ n) M).move i).move j) hpG'' hnG'',
    end
using_well_founded {dec_tac := tactic.assumption}
