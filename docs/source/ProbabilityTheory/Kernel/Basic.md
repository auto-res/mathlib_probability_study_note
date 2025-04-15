ProbabilityTheory.Kernel.Basic
==========================================
このファイルではカーネルの基本的な定義や性質を列挙します.

``` lean4
/-- Constant kernel, which always returns the same measure. -/
def const (α : Type*) {β : Type*} [MeasurableSpace α] {_ : MeasurableSpace β} (μβ : Measure β) :
    Kernel α β where
  toFun _ := μβ
  measurable' := measurable_const
```

