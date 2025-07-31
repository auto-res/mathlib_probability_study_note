MeasureTheory.OuterMeasure.OfFunction
============================================

このファイルでは関数から外測度を構成します.(外測度の別定義として知られる)

コード元
[MeasureTheory.OuterMeasure.OfFunction](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/OuterMeasure/OfFunction.html)

``` lean4
/-- Given any function `m` assigning measures to sets satisfying `m ∅ = 0`, there is
  a unique maximal outer measure `μ` satisfying `μ s ≤ m s` for all `s : Set α`. -/
protected def ofFunction (m : Set α → ℝ≥0∞) (m_empty : m ∅ = 0) : OuterMeasure α :=
  let μ s := ⨅ (f : ℕ → Set α) (_ : s ⊆ ⋃ i, f i), ∑' i, m (f i)
  { measureOf := μ
    empty :=
      le_antisymm
        ((iInf_le_of_le fun _ => ∅) <| iInf_le_of_le (empty_subset _) <| by simp [m_empty])
        (zero_le _)
    mono := fun {_ _} hs => iInf_mono fun _ => iInf_mono' fun hb => ⟨hs.trans hb, le_rfl⟩
    iUnion_nat := fun s _ =>
      ENNReal.le_of_forall_pos_le_add <| by
        intro ε hε (hb : (∑' i, μ (s i)) < ∞)
        rcases ENNReal.exists_pos_sum_of_countable (ENNReal.coe_pos.2 hε).ne' ℕ with ⟨ε', hε', hl⟩
        refine le_trans ?_ (add_le_add_left (le_of_lt hl) _)
        rw [← ENNReal.tsum_add]
        choose f hf using
          show ∀ i, ∃ f : ℕ → Set α, (s i ⊆ ⋃ i, f i) ∧ (∑' i, m (f i)) < μ (s i) + ε' i by
            intro i
            have : μ (s i) < μ (s i) + ε' i :=
              ENNReal.lt_add_right (ne_top_of_le_ne_top hb.ne <| ENNReal.le_tsum _)
                (by simpa using (hε' i).ne')
            rcases iInf_lt_iff.mp this with ⟨t, ht⟩
            exists t
            contrapose! ht
            exact le_iInf ht
        refine le_trans ?_ (ENNReal.tsum_le_tsum fun i => le_of_lt (hf i).2)
        rw [← ENNReal.tsum_prod, ← Nat.pairEquiv.symm.tsum_eq]
        refine iInf_le_of_le _ (iInf_le _ ?_)
        apply iUnion_subset
        intro i
        apply Subset.trans (hf i).1
        apply iUnion_subset
        simp only [Nat.pairEquiv_symm_apply]
        rw [iUnion_unpair]
        intro j
        apply subset_iUnion₂ i }
```
集合$s$を高々可算無限個の$f_{i \in \mathbb{N}}$で覆い, $\mu(s) = \inf \sum\limits_{i=0}^\infty m (f_i)$ で定義すると, $\mu$は外測度になります.