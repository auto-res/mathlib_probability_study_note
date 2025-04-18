MeasureTheory.MeasureSpace.Defs
============================================

このファイルでは可測空間, $\sigma$-加法族, 可測関数の定義を行います.

コード元
[MeasureTheory.MeasurableSpace.Defs](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/MeasurableSpace/Defs.html)

``` lean4
/-- A measurable space is a space equipped with a σ-algebra. -/
@[class] structure MeasurableSpace (α : Type*) where
  /-- Predicate saying that a given set is measurable. Use `MeasurableSet` in the root namespace
  instead. -/
  MeasurableSet' : Set α → Prop
  /-- The empty set is a measurable set. Use `MeasurableSet.empty` instead. -/
  measurableSet_empty : MeasurableSet' ∅
  /-- The complement of a measurable set is a measurable set. Use `MeasurableSet.compl` instead. -/
  measurableSet_compl : ∀ s, MeasurableSet' s → MeasurableSet' sᶜ
  /-- The union of a sequence of measurable sets is a measurable set. Use a more general
  `MeasurableSet.iUnion` instead. -/
  measurableSet_iUnion : ∀ f : ℕ → Set α, (∀ i, MeasurableSet' (f i)) → MeasurableSet' (⋃ i, f i)

instance [h : MeasurableSpace α] : MeasurableSpace αᵒᵈ := h

/-- `MeasurableSet s` means that `s` is measurable (in the ambient measure space on `α`) -/
def MeasurableSet [MeasurableSpace α] (s : Set α) : Prop :=
  ‹MeasurableSpace α›.MeasurableSet' s

/-- Notation for `MeasurableSet` with respect to a non-standard σ-algebra. -/
scoped[MeasureTheory] notation "MeasurableSet[" m "]" => @MeasurableSet _ m
```
これは可測空間の定義です. 可測性を持つ(`measurableSet_empty`, `measurableSet_compl`, `measurableSet_iUnion`)集合族(`MeasurableSet' : Set α → Prop`)である$\sigma$-加法族が型クラスとして機能する構造体として定義されています.

``` lean4
/-- A function `f` between measurable spaces is measurable if the preimage of every
  measurable set is measurable. -/
@[fun_prop]
def Measurable [MeasurableSpace α] [MeasurableSpace β] (f : α → β) : Prop :=
  ∀ ⦃t : Set β⦄, MeasurableSet t → MeasurableSet (f ⁻¹' t)
```
これは可測関数の定義です. 可測関数は, その逆像が$\sigma$-加法族であることを要求します. `Measurable`に関する簡単な主張を見ていきましょう. ちなみに, 逆像の定義は以下のように定義されます.
``` lean4
/-- The preimage of `s : Set β` by `f : α → β`, written `f ⁻¹' s`,
  is the set of `x : α` such that `f x ∈ s`. -/
def preimage (f : α → β) (s : Set β) : Set α := {x | f x ∈ s}

/-- `f ⁻¹' t` denotes the preimage of `t : Set β` under the function `f : α → β`. -/
infixl:80 " ⁻¹' " => preimage
```

``` lean4
protected theorem Measurable.comp {_ : MeasurableSpace α} {_ : MeasurableSpace β}
    {_ : MeasurableSpace γ} {g : β → γ} {f : α → β} (hg : Measurable g) (hf : Measurable f) :
    Measurable (g ∘ f) :=
  fun _ h => hf (hg h)
```
これは合成関数の可測性を示しています.

``` lean4
protected theorem MeasurableSet.const (p : Prop) : MeasurableSet { _a : α | p } := by
  by_cases p <;> simp [*]

@[simp, fun_prop, measurability]
theorem measurable_const {_ : MeasurableSpace α} {_ : MeasurableSpace β} {a : α} :
    Measurable fun _ : β => a := fun s _ => .const (a ∈ s)
```
`MeasurableSet.const`について`{ _a : α | (p : Prop) }`は`p`が真であるときにunivとなり, 偽であるときにemptyとなるのでどちらも$\sigma$-加法族です. `measurable_const`は`MeasurableSet.const`にPropである`a ∈ s`を適用することでBoolから任意の型に拡張した形で定数関数が可測であることを示しています.
