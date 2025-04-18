MeasureTheory.MeasureSpace.Lebesgue
============================================

このファイルでは下ルベーグ積分の定義を行います.

コード元
[MeasureTheory.MeasurableSpace.Lebesgue](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.html)

``` lean4
/-- The **lower Lebesgue integral** of a function `f` with respect to a measure `μ`. -/
irreducible_def lintegral {_ : MeasurableSpace α} (μ : Measure α) (f : α → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ (g : α →ₛ ℝ≥0∞) (_ : ⇑g ≤ f), g.lintegral μ
```
`g ≤ f`を満たす単関数`g`の中で積分が最大となるものを`lintegral`で定義します.

``` lean4
@[inherit_doc MeasureTheory.lintegral]
notation3 "∫⁻ "(...)", "r:60:(scoped f => f)" ∂"μ:70 => lintegral μ r

@[inherit_doc MeasureTheory.lintegral]
notation3 "∫⁻ "(...)", "r:60:(scoped f => lintegral volume f) => r
```
`lintegral`は上記のように積分の記法でも書けます.