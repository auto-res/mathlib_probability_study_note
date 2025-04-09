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

``` lean4
/-- A function is almost everywhere measurable if it coincides almost everywhere with a measurable
function. -/
@[fun_prop]
def AEMeasurable {_m : MeasurableSpace α} (f : α → β) (μ : Measure α := by volume_tac) : Prop :=
  ∃ g : α → β, Measurable g ∧ f =ᵐ[μ] g

@[fun_prop, aesop unsafe 30% apply (rule_sets := [Measurable])]
theorem Measurable.aemeasurable (h : Measurable f) : AEMeasurable f μ :=
  ⟨f, h, ae_eq_refl f⟩
```