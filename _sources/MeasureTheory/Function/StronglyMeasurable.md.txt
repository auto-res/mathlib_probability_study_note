MeasureTheory.MeasureSpace.StronglyMeasurable
============================================

このファイルでは強可測の定義を行います.

コード元
[MeasureTheory.MeasurableSpace.StronglyMeasurable](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/StronglyMeasurable/Basic.html)

``` lean4
variable {α β γ ι : Type*} [Countable ι]

namespace MeasureTheory

local infixr:25 " →ₛ " => SimpleFunc

section Definitions

variable [TopologicalSpace β]

/-- A function is `StronglyMeasurable` if it is the limit of simple functions. -/
def StronglyMeasurable [MeasurableSpace α] (f : α → β) : Prop :=
  ∃ fs : ℕ → α →ₛ β, ∀ x, Tendsto (fun n => fs n x) atTop (nhds (f x))
```

ある単関数列`fs`が存在して, すべての`x`で`f x`の近傍の極限に, 単関数の値`fs n x`が収束することを要求しています.

``` lean4
/-- The notation for StronglyMeasurable giving the measurable space instance explicitly. -/
scoped notation "StronglyMeasurable[" m "]" => @MeasureTheory.StronglyMeasurable _ _ _ m
```

mが強可測であることは`StronglyMeasurable[m]`と略記できます.