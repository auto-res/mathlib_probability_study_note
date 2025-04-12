MeasureTheory.MeasureSpace.Lebesgue
============================================

このファイルでは単関数の積分の定義を行います.

コード元
[MeasureTheory.MeasurableSpace.SimpleFunc](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/MeasurableSpace/SimpleFunc.html)

``` lean4
/-- A function `f` from a measurable space to any type is called *simple*,
if every preimage `f ⁻¹' {x}` is measurable, and the range is finite. This structure bundles
a function with these properties. -/
structure SimpleFunc.{u, v} (α : Type u) [MeasurableSpace α] (β : Type v) where
  toFun : α → β
  measurableSet_fiber' : ∀ x, MeasurableSet (toFun ⁻¹' {x})
  finite_range' : (Set.range toFun).Finite
```

`SimpleFunc`は可測空間から任意の型への単関数を表します. `toFun`はその関数を表し, `measurableSet_fiber'`はその逆像が常に可測であることを示しています. `finite_range'`はその値域が有限であることを示しています.

``` lean4
local infixr:25 " →ₛ " => SimpleFunc
```
単関数は以上の記法で表すこともできます.

``` lean4
/-- Integral of a simple function whose codomain is `ℝ≥0∞`. -/
def lintegral {_m : MeasurableSpace α} (f : α →ₛ ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  ∑ x ∈ f.range, x * μ (f ⁻¹' {x})
```
`lintegral`は単関数の積分を定義しています. `f.range`はその値域を表します. `μ (f ⁻¹' {x})`はその逆像の測度を表します. `x * μ (f ⁻¹' {x})`はその測度に対する重み付けを行っています.
