MeasureTheory.Function.Integrable
============================================

コード元
[MeasureTheory.Function.Integrable](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/L1Space/Integrable.html)

``` lean4
/-- `Integrable f μ` means that `f` is measurable and that the integral `∫⁻ a, ‖f a‖ ∂μ` is finite.
  `Integrable f` means `Integrable f volume`. -/
@[fun_prop]
def Integrable {α} {_ : MeasurableSpace α} (f : α → ε)
    (μ : Measure α := by volume_tac) : Prop :=
  AEStronglyMeasurable f μ ∧ HasFiniteIntegral f μ
```
可積分性を示すにはほとんど至る所で強可測(`AEStronglyMeasurable`)であり,かつ絶対可積分性(`HasFiniteIntegral`)を満たす必要があります.