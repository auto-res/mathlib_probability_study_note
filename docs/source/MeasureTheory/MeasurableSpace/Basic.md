MeasureTheory.MeasureSpace.Basic
============================================

このファイルでは可測空間の基本的な性質が列挙されています.

コード元
[MeasureTheory.MeasurableSpace.Basic](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/MeasurableSpace/Basic.html)

``` lean4
/-- The forward image of a measurable space under a function. `map f m` contains the sets
  `s : Set β` whose preimage under `f` is measurable. -/
protected def map (f : α → β) (m : MeasurableSpace α) : MeasurableSpace β where
  MeasurableSet' s := MeasurableSet[m] <| f ⁻¹' s
  measurableSet_empty := m.measurableSet_empty
  measurableSet_compl _ hs := m.measurableSet_compl _ hs
  measurableSet_iUnion f hf := by simpa only [preimage_iUnion] using m.measurableSet_iUnion _ hf
```
可測空間mの集合族である$\sigma$-加法族のfによる押し出しです. MeasurableSpace.map mは$\sigma$-加法族になります.

``` lean4
/-- The reverse image of a measurable space under a function. `comap f m` contains the sets
  `s : Set α` such that `s` is the `f`-preimage of a measurable set in `β`. -/
protected def comap (f : α → β) (m : MeasurableSpace β) : MeasurableSpace α where
  MeasurableSet' s := ∃ s', MeasurableSet[m] s' ∧ f ⁻¹' s' = s
  measurableSet_empty := ⟨∅, m.measurableSet_empty, rfl⟩
  measurableSet_compl := fun _ ⟨s', h₁, h₂⟩ => ⟨s'ᶜ, m.measurableSet_compl _ h₁, h₂ ▸ rfl⟩
  measurableSet_iUnion s hs :=
    let ⟨s', hs'⟩ := Classical.axiom_of_choice hs
    ⟨⋃ i, s' i, m.measurableSet_iUnion _ fun i => (hs' i).left, by simp [hs']⟩
```
可測空間mの集合族である$\sigma$-加法族のfによる引き戻しです. MeasurableSpace.comap mは$\sigma$-加法族になります. `measurableSet_iUnion`について証明の途中で, 等式$f^{-1} \bigcup_{\lambda \in \Lambda} X = \bigcup_{\lambda \in \Lambda} f^{-1} X$が使われますが, ここで選択公理が暗に使われています.