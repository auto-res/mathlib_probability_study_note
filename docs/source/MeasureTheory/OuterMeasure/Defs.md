MeasureTheory.OuterMeasure.Defs
============================================

このファイルでは外測度を定義しています. また測度論に関する他のファイルをimportしていない測度論の最も基本的なファイルの一つになります

コード元
[MeasureTheory.OuterMeasure.Defs](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/OuterMeasure/Defs.html)

``` lean4
/-- An outer measure is a countably subadditive monotone function that sends `∅` to `0`. -/
structure OuterMeasure (α : Type*) where
  /-- Outer measure function. Use automatic coercion instead. -/
  protected measureOf : Set α → ℝ≥0∞
  protected empty : measureOf ∅ = 0
  protected mono : ∀ {s₁ s₂}, s₁ ⊆ s₂ → measureOf s₁ ≤ measureOf s₂
  protected iUnion_nat : ∀ s : ℕ → Set α, Pairwise (Disjoint on s) →
    measureOf (⋃ i, s i) ≤ ∑' i, measureOf (s i)
```

