ProbabilityTheory.Kernel.Defs
==================================

このファイルでは確率論で条件つき確率や独立を扱う際の基礎となるkernelの定義を行います. 

``` lean4
/-- A kernel from a measurable space `α` to another measurable space `β` is a measurable function
`κ : α → Measure β`. The measurable space structure on `MeasureTheory.Measure β` is given by
`MeasureTheory.Measure.instMeasurableSpace`. A map `κ : α → MeasureTheory.Measure β` is measurable
iff `∀ s : Set β, MeasurableSet s → Measurable (fun a ↦ κ a s)`. -/
structure Kernel (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] where
  /-- The underlying function of a kernel.

  Do not use this function directly. Instead use the coercion coming from the `DFunLike`
  instance. -/
  toFun : α → Measure β
  /-- A kernel is a measurable map.

  Do not use this lemma directly. Use `Kernel.measurable` instead. -/
  measurable' : Measurable toFun
```

kernelは測度空間`α`から測度空間`β`への可測関数であり, その値は測度です. つまり`κ`をkernelとすると, `κ (a : α) (s : Set β)`は非負の実数を返します.

``` lean4
/-- A kernel is a Markov kernel if every measure in its image is a probability measure. -/
class IsMarkovKernel (κ : Kernel α β) : Prop where
  isProbabilityMeasure : ∀ a, IsProbabilityMeasure (κ a)
```

値域の測度が確率測度であるとき, kernelはMarkov kernelと呼ばれます. 
