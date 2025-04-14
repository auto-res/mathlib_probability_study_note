MeasureTheory.Measure.MeasureSpaceDef
============================================

このファイルでは測度の定義を行います.

コード元
[MeasureTheory.Measure.MeasureSpaceDef](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.html)

``` lean4
/-- A measure is defined to be an outer measure that is countably additive on
measurable sets, with the additional assumption that the outer measure is the canonical
extension of the restricted measure. -/
structure Measure (α : Type*) [MeasurableSpace α] extends OuterMeasure α where
  m_iUnion ⦃f : ℕ → Set α⦄ : (∀ i, MeasurableSet (f i)) → Pairwise (Disjoint on f) →
    toOuterMeasure (⋃ i, f i) = ∑' i, toOuterMeasure (f i)
  trim_le : toOuterMeasure.trim ≤ toOuterMeasure
```
`m_iUnion`は可算加法性を示しています. これはOuterMeasureの`iUnion_nat`(可算劣加法性)より強いです. 
`trim_le`は外測度の可測集合への制限が元の外測度より小さいことを述べています. `toOuterMeasure`は`OuterMeasure α`の型を持ちます.
``` lean4
theorem trimmed (μ : Measure α) : μ.toOuterMeasure.trim = μ.toOuterMeasure :=
  le_antisymm μ.trim_le μ.1.le_trim
```
すべての外測度で成り立つ`le_trim`と合わせると, `toOuterMeasure.trim = toOuterMeasure`が成り立ちます.

``` lean4
/-- A measure space is a measurable space equipped with a
  measure, referred to as `volume`. -/
class MeasureSpace (α : Type*) extends MeasurableSpace α where
  volume : Measure α
```
測度空間`MeasureSpace`は可測空間に測度を付与したものです. `volume`はその測度を表し, OuterMeasureの性質と`m_iUnion`, `trim_le`を満たします.

``` lean4
/-- The tactic `exact volume`, to be used in optional (`autoParam`) arguments. -/
macro "volume_tac" : tactic =>
  `(tactic| (first | exact MeasureTheory.MeasureSpace.volume))
```
TODO

``` lean4
lemma ae_eq_refl (f : α → β) : f =ᵐ[μ] f := EventuallyEq.rfl

/-- A function is almost everywhere measurable if it coincides almost everywhere with a measurable
function. -/
@[fun_prop]
def AEMeasurable {_m : MeasurableSpace α} (f : α → β) (μ : Measure α := by volume_tac) : Prop :=
  ∃ g : α → β, Measurable g ∧ f =ᵐ[μ] g

@[fun_prop, aesop unsafe 30% apply (rule_sets := [Measurable])]
theorem Measurable.aemeasurable (h : Measurable f) : AEMeasurable f μ :=
  ⟨f, h, ae_eq_refl f⟩
```

`AEMeasurable`は$\mu-a.e.$で同一視できる可測関数を持つことを示しています.
`Measurable.aemeasurable`はAEMeasurableのgに自分自身(f)を入れることによって示すことができます. `ae_eq_refl`は`f =ᵐ[μ] f`を示しています.