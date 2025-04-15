MeasureTheory.Measure.GiryMonad
=====================================

``` lean4
/-- Monadic join on `Measure` in the category of measurable spaces and measurable
functions. -/
def join (m : Measure (Measure α)) : Measure α :=
  Measure.ofMeasurable (fun s _ => ∫⁻ μ, μ s ∂m)
    (by simp only [measure_empty, lintegral_const, zero_mul])
    (by
      intro f hf h
      simp_rw [measure_iUnion h hf]
      apply lintegral_tsum
      intro i; exact (measurable_coe (hf i)).aemeasurable)
```
`join`は測度の測度を測度に戻す操作です. これはモナドにおける`join`に相当します.
`fun s _ => ∫⁻ μ, μ s ∂m`は`(s : Set α) → MeasurableSet s → ℝ≥0∞`を型に持ち, `(by simp only [measure_empty, lintegral_const, zero_mul])`は`(fun s x ↦ ∫⁻ (μ : Measure α), μ s ∂m) ∅ ⋯ = 0`を示し,

``` lean4
(by
    intro f hf h
    simp_rw [measure_iUnion h hf]
    apply lintegral_tsum
    intro i; exact (measurable_coe (hf i)).aemeasurable)
```
は以下を示しています.
``` lean4
∀ ⦃f : ℕ → Set α⦄ (h : ∀ (i : ℕ), MeasurableSet (f i)),
  Pairwise (Function.onFun Disjoint f) →
    (fun s x ↦ ∫⁻ (μ : Measure α), μ s ∂m) (⋃ i, f i) ⋯ = ∑' (i : ℕ), (fun s x ↦ ∫⁻ (μ : Measure α), μ s ∂m) (f i) ⋯
```

``` lean4
/-- Monadic bind on `Measure`, only works in the category of measurable spaces and measurable
functions. When the function `f` is not measurable the result is not well defined. -/
def bind (m : Measure α) (f : α → Measure β) : Measure β :=
  join (map f m)
```
これはモナドにおける`bind`に相当します.
``` lean4
`map f m`の型は`Measure (Measure β)`であるので`join`の引数と型が一致します.

``` lean4
variable {μ : Measure α} {κ : Kernel α β}

/-- Composition of a measure and a kernel.

Notation for `MeasureTheory.Measure.bind` -/
scoped[ProbabilityTheory] notation:100 κ:101 " ∘ₘ " μ:100 => MeasureTheory.Measure.bind μ κ

```
`μ`が測度で`κ`がカーネルであるとき, つまりbindの定義における`f`が可測関数の時, `MeasureTheory.Measure.bind`は` ∘ₘ `を使って書くこともできます.