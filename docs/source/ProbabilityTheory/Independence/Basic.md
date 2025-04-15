ProbabilityTheory.Independence.Basic
=========================================

このファイルでは[ProbabilityTheory.Independence.Kernel](Kernel.md)で定義したカーネルによる独立性を用いて, 測度から独立性を定義します.

まず, 独立性の定義に使われる`Kernel.const`と`Measure.dirac`の定義を見ます.(他のファイルから参照)
``` lean4
/-- Constant kernel, which always returns the same measure. -/
def const (α : Type*) {β : Type*} [MeasurableSpace α] {_ : MeasurableSpace β} (μβ : Measure β) :
    Kernel α β where
  toFun _ := μβ
  measurable' := measurable_const
```
Constant Kernelとは, どんな引数を与えても同じ測度を返す関数です.また, この関数は可測になっています.

``` lean4
/-- The dirac outer measure. -/
def dirac (a : α) : OuterMeasure α where
  measureOf s := indicator s (fun _ => 1) a
  empty := by simp
  mono {_ _} h := indicator_le_indicator_of_subset h (fun _ => zero_le _) a
  iUnion_nat s _ := calc
    indicator (⋃ n, s n) 1 a = ⨆ n, indicator (s n) 1 a :=
      indicator_iUnion_apply (M := ℝ≥0∞) rfl _ _ _
    _ ≤ ∑' n, indicator (s n) 1 a := iSup_le fun _ ↦ ENNReal.le_tsum _

/-- The dirac measure. -/
def dirac (a : α) : Measure α := (OuterMeasure.dirac a).toMeasure (by simp)
```
Dirac measureは, Dirac outer measureを使って定義されます. Dirac outer measureは, 指示関数を使って定義されていて, `s`が`a`である時は1, それ以外は0を返します. Dirac measureはDirac outer measureを使って定義されていて, Dirac outer measureの性質を引き継いでいます.

``` lean4
/-- A family of measurable space structures (i.e. of σ-algebras) is independent with respect to a
measure `μ` (typically defined on a finer σ-algebra) if the family of sets of measurable sets they
define is independent. `m : ι → MeasurableSpace Ω` is independent with respect to measure `μ` if
for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ m i_1, ..., f i_n ∈ m i_n`, then `μ (⋂ i in s, f i) = ∏ i ∈ s, μ (f i)`. -/
def iIndep (m : ι → MeasurableSpace Ω) {_mΩ : MeasurableSpace Ω} (μ : Measure Ω := by volume_tac) :
    Prop :=
  Kernel.iIndep m (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)
```

`Unit`はただ一つの要素`()`を持つ標準(canonical)な型です. また, ここでは`Unit`は多相的に使われています.

添え字付きの可測空間が独立であるとは入力値によらない定数カーネルについて任意の有限個の添え字の集合が独立である(`Kernel.iIndep`)ことと定義します.

``` lean4
/-- Two measurable space structures (or σ-algebras) `m₁, m₂` are independent with respect to a
measure `μ` (defined on a third σ-algebra) if for any sets `t₁ ∈ m₁, t₂ ∈ m₂`,
`μ (t₁ ∩ t₂) = μ (t₁) * μ (t₂)` -/
def Indep (m₁ m₂ : MeasurableSpace Ω)
    {_mΩ : MeasurableSpace Ω} (μ : Measure Ω := by volume_tac) : Prop :=
  Kernel.Indep m₁ m₂ (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)
```

添え字付きの可測空間が独立であるとは入力値によらない定数カーネルに関して任意の集合が独立である(`Kernel.Indep`)ことと定義します.