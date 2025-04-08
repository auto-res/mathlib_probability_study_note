MeasureTheory.OuterMeasure.AE
============================================
このファイルでは外測度の零集合の補集合`s ∈ ae μ ↔ μ sᶜ = 0`を定義しています. 

``` lean4
/-- The “almost everywhere” filter of co-null sets. -/
def ae (μ : F) : Filter α :=
  .ofCountableUnion (μ · = 0) (fun _S hSc ↦ (measure_sUnion_null_iff hSc).2) fun _t ht _s hs ↦
    measure_mono_null hs ht

/-- `∀ᵐ a ∂μ, p a` means that `p a` for a.e. `a`, i.e. `p` holds true away from a null set.

This is notation for `Filter.Eventually p (MeasureTheory.ae μ)`. -/
notation3 "∀ᵐ "(...)" ∂"μ", "r:(scoped p => Filter.Eventually p <| MeasureTheory.ae μ) => r
```

`measure_sUnion_null_iff`とはMeasureTheory.OuterMeasure.Basicで, `Filter.ofCountableUnion`はOrder.Filter.CountableInterで定義されています. それぞれについてコードを見ることで`ae`の定義を理解しましょう.

``` lean4
theorem measure_sUnion_null_iff {S : Set (Set α)} (hS : S.Countable) :
    μ (⋃₀ S) = 0 ↔ ∀ s ∈ S, μ s = 0 := by
  rw [sUnion_eq_biUnion, measure_biUnion_null_iff hS]

theorem measure_mono_null (h : s ⊆ t) (ht : μ t = 0) : μ s = 0 :=
  eq_bot_mono (measure_mono h) ht
```
`measure_sUnion_null_iff`は可算個の集合の合併が零集合であることと, 各集合が零集合であることが同値であることを示しています. `measure_mono_null`は包含関係と零集合の条件から, 零集合であることを示しています.

``` lean4
/-- Construct a filter with countable intersection property. This constructor deduces
`Filter.univ_sets` and `Filter.inter_sets` from the countable intersection property. -/
def Filter.ofCountableInter (l : Set (Set α))
    (hl : ∀ S : Set (Set α), S.Countable → S ⊆ l → ⋂₀ S ∈ l)
    (h_mono : ∀ s t, s ∈ l → s ⊆ t → t ∈ l) : Filter α where
  sets := l
  univ_sets := @sInter_empty α ▸ hl _ countable_empty (empty_subset _)
  sets_of_superset := h_mono _ _
  inter_sets {s t} hs ht := sInter_pair s t ▸
    hl _ ((countable_singleton _).insert _) (insert_subset_iff.2 ⟨hs, singleton_subset_iff.2 ht⟩)

/-- Construct a filter with countable intersection property.
Similarly to `Filter.comk`, a set belongs to this filter if its complement satisfies the property.
Similarly to `Filter.ofCountableInter`,
this constructor deduces some properties from the countable intersection property
which becomes the countable union property because we take complements of all sets. -/
def Filter.ofCountableUnion (l : Set (Set α))
    (hUnion : ∀ S : Set (Set α), S.Countable → (∀ s ∈ S, s ∈ l) → ⋃₀ S ∈ l)
    (hmono : ∀ t ∈ l, ∀ s ⊆ t, s ∈ l) : Filter α := by
  refine .ofCountableInter {s | sᶜ ∈ l} (fun S hSc hSp ↦ ?_) fun s t ht hsub ↦ ?_
  · rw [mem_setOf_eq, compl_sInter]
    apply hUnion (compl '' S) (hSc.image _)
    intro s hs
    rw [mem_image] at hs
    rcases hs with ⟨t, ht, rfl⟩
    apply hSp ht
  · rw [mem_setOf_eq]
    rw [← compl_subset_compl] at hsub
    exact hmono sᶜ ht tᶜ hsub
```

`Filter.ofCountableInter`と`Filter.CountableUnion`は包含関係について逆の関係になっています. `Filter.CountableUnion`は要素である集合の補集合を要素とする集合族が`Filter.ofCountableInter`を満たすことを示すことによって証明されます.
`Filter.ofCountableInter`は可算交叉の性質を持ち(`hUnion`), 上方向に閉じて(`hmono`)いる時, それはフィルタであることを示しています. つまり`ae`は可算交叉の性質を持っていることに注意してください.

`ae`の型を確認してみましょう. `(μ · = 0)`は`Set α → Prop`, `(fun _S hSc ↦ (measure_sUnion_null_iff hSc).2)`は`∀ (_S : Set (Set α)), _S.Countable → (∀ s ∈ _S, μ s = 0) → μ (⋃₀ _S) = 0`, `fun _t ht _s hs ↦ measure_mono_null hs ht`は`∀ _t ∈ fun x ↦ μ x = 0, ∀ _s ⊆ _t, μ _s = 0`という型を持っています. 一見これは`Filter.CountableUnion`に合致していないように見えますが, Setの型が
``` lean4
def Set (α : Type u) := α → Prop
```
で特性関数と同一視する形で定義されているので, 正しく`Filter.CountableUnion`の型を満たしています.

``` lean4
theorem ae_of_all {p : α → Prop} (μ : F) : (∀ a, p a) → ∀ᵐ a ∂μ, p a :=
  Eventually.of_forall
```
`∀ᵐ a ∂μ, p a`は`{a | p a} ∈ ae μ`と定義されることに注意すると,`Eventually.of_forall`により直接従います.